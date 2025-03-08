//
// simulans
//
// Copyright 2025- Manos Pitsidianakis
//
// This file is part of simulans.
//
// simulans is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// simulans is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with simulans. If not, see <http://www.gnu.org/licenses/>.
//
// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later

use std::{ops::ControlFlow, pin::Pin};

use cranelift::{codegen::ir::immediates::Offset32, prelude::*};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use indexmap::IndexMap;

use crate::{cpu_state::ExecutionState, machine::Armv8AMachine};

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct Entry(pub extern "C" fn(&mut JitContext, &mut Armv8AMachine) -> Entry);

pub extern "C" fn lookup_entry(context: &mut JitContext, machine: &mut Armv8AMachine) -> Entry {
    let pc: u64 = machine.pc;
    if let Some(entry) = machine.entry_blocks.get(&pc) {
        log::trace!("lookup entry entry found for {}", pc);
        return *entry;
    }
    log::trace!("generating entry for pc {}", pc);

    let next_entry = context.compile(machine, pc.try_into().unwrap()).unwrap();
    machine.entry_blocks.insert(pc, next_entry);

    log::trace!("returning generated entry for pc {}", pc);
    next_entry
}

pub struct JitContext {
    /// The function builder context, which is reused across multiple
    /// FunctionBuilder instances.
    builder_context: FunctionBuilderContext,
    /// The main Cranelift context, which holds the state for codegen. Cranelift
    /// separates this from `Module` to allow for parallel compilation, with a
    /// context per thread.
    ctx: codegen::Context,
    /// The module, with the jit backend, which manages the JIT'd
    /// functions.
    module: JITModule,
}

impl JitContext {
    pub fn new() -> Pin<Box<Self>> {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        let module = JITModule::new(builder);
        Box::pin(Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            module,
        })
    }

    pub fn compile(
        &mut self,
        machine: &mut Armv8AMachine,
        program_counter: usize,
    ) -> Result<Entry, Box<dyn std::error::Error>> {
        log::trace!("jit compile called for pc = {}", program_counter);
        let mut sig = self.module.make_signature();
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        sig.params
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        sig.returns
            .push(AbiParam::new(self.module.target_config().pointer_type()));
        self.ctx.func.signature = sig;
        // self.ctx.set_disasm(true);

        // Actually perform the translation for this translation block
        self.translate(machine, program_counter)?;

        // Functions must be declared before they can be called, or defined.
        let id = self.module.declare_function(
            &format!("0x{program_counter:x}"),
            Linkage::Export,
            &self.ctx.func.signature,
        )?;

        // Define the function to jit. This finishes compilation.
        self.module.define_function(id, &mut self.ctx)?;

        // {
        //     let pc = program_counter;
        //     log::trace!("cranelift IR for translation block at pc={pc:#x}:");
        //     log::trace!("{}", self.ctx.func);
        //     log::trace!("Native generated code for translation block at
        // pc={pc:#x}:");     log::trace!(
        //         "{}",
        //         self.ctx.compiled_code().unwrap().vcode.as_ref().unwrap()
        //     );
        // }

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(&mut self.ctx);

        // We don't call any symbols.
        self.module.finalize_definitions().unwrap();

        // We can now retrieve a pointer to the machine code.
        // SAFETY: the function signature has been defined to take two pointers as
        // parameters and return a pointer. This is safe to transmute as long as
        // we hold the contract that the generated function has this type.
        let code = unsafe {
            std::mem::transmute::<
                *const u8,
                for<'a, 'b> extern "C" fn(&'a mut JitContext, &'b mut Armv8AMachine) -> Entry,
            >(self.module.get_finalized_function(id))
        };

        Ok(Entry(code))
    }

    // Translate instructions starting from address `program_counter`.
    fn translate(
        &mut self,
        machine: &mut Armv8AMachine,
        program_counter: usize,
    ) -> Result<(), Box<dyn std::error::Error>> {
        use std::ops::Deref;

        let machine_addr = std::ptr::addr_of!(*machine);
        let self_addr = std::ptr::addr_of!(*self);

        let Armv8AMachine {
            ref mut mem,
            ref mut cpu_state,
            ..
        } = machine;
        let decoded_iter =
            bad64::disasm(&mem.map.deref()[program_counter..], program_counter as u64);

        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        builder.append_block_params_for_function_params(entry_block);

        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        let mut registers = IndexMap::new();
        let mut sys_registers = IndexMap::new();

        // Declare variables for each register.
        // Emit code to load register values into variables.
        cpu_state.load_cpu_state(&mut builder, &mut registers, &mut sys_registers);
        let jit_ctx_ptr = builder
            .ins()
            .iconst(self.module.target_config().pointer_type(), self_addr as i64);
        let machine_ptr = builder.ins().iconst(
            self.module.target_config().pointer_type(),
            machine_addr as i64,
        );
        let sigref = builder.import_signature(builder.func.signature.clone());
        let mut trans = FunctionTranslator {
            int,
            pointer_type: self.module.target_config().pointer_type(),
            mem_start: mem.map.as_ptr() as usize as i64,
            cpu_state,
            jit_ctx_ptr,
            machine_ptr,
            sigref,
            builder,
            registers,
            sys_registers,
        };
        let mut next_pc = None;
        // Translate each decoded instruction
        for insn in decoded_iter {
            match insn {
                Ok(insn) => {
                    log::trace!("{:#?}", insn);
                    log::trace!("{}", insn);
                    if let ControlFlow::Break(jump_pc) = trans.translate_instruction(insn) {
                        next_pc = jump_pc;
                        break;
                    }
                }
                Err(err) => {
                    log::error!("Error decoding instruction: {}", err);
                }
            }
        }
        if let Some(next_pc) = next_pc {
            trans.emit_jump(next_pc);
        } else {
            // We are out of code, so halt the machine
            trans.emit_halt();
        }
        let FunctionTranslator { builder, .. } = trans;

        // Tell the builder we're done with this function.
        builder.finalize();
        Ok(())
    }
}

/// In-progress state of translating instructions into Cranelift IR.
struct FunctionTranslator<'a> {
    int: types::Type,
    mem_start: i64,
    builder: FunctionBuilder<'a>,
    cpu_state: &'a mut ExecutionState,
    jit_ctx_ptr: Value,
    machine_ptr: Value,
    pointer_type: Type,
    sigref: codegen::ir::SigRef,
    registers: IndexMap<bad64::Reg, Variable>,
    sys_registers: IndexMap<bad64::SysReg, Variable>,
}

impl FunctionTranslator<'_> {
    #[allow(non_snake_case)]
    fn translate_o0_op1_CRn_CRm_op2(&mut self, o0: u8, o1: u8, cm: u8, cn: u8, o2: u8) -> Value {
        match (o0, o1, cm, cn, o2) {
            (0b11, 0, 0, 0b111, 0) => {
                // ID_AA64MMFR0_EL1
                // FIXME
                self.builder.ins().iconst(self.int, 0)
            }
            (0b11, 0, 0, 0, 0) => {
                // MIDR_EL1
                // FIXME
                self.builder.ins().iconst(self.int, 0)
            }
            (3, 0, 0, 0, 5) => {
                // MPIDR_EL1
                // FIXME
                self.builder.ins().iconst(self.int, 0)
            }
            _other => unimplemented!(
                "unimplemented sysreg encoding: {:?}",
                bad64::Operand::ImplSpec { o0, o1, cm, cn, o2 }
            ),
        }
    }

    fn translate_cmp_64(&mut self, _instruction: &bad64::Instruction) -> Value {
        // let a = self.translate_operand(&instruction.operands()[1]);
        // let b = self.translate_operand(&instruction.operands()[2]);
        // let (svalue, _overflow_flag) = self.builder.ins().sadd_overflow(a, b);
        // let (uvalue, _overflow_flag) = self.builder.ins().uadd_overflow(a, b);
        // let n = self.builder.ins().band(svalue, 0x1 << 64);
        // let zero = self.reg_to_value(&bad64::Reg::XZR);
        // let n_cond = self
        //     .builder
        //     .ins()
        //     .icmp(cranelift::prelude::IntCC::Equal, n, zero);

        // let zero_block = self.builder.create_block();
        // let else_block = self.builder.create_block();
        // let merge_block = self.builder.create_block();
        // self.builder
        //     .ins()
        //     .brif(n_cond, zero_block, &[], else_block, &[]);

        /*
                 / AddWithCarry()
        // ==============
        // Integer addition with carry input, returning result and NZCV flags

        (bits(N), bits(4)) AddWithCarry(bits(N) x, bits(N) y, bit carry_in)
            constant integer unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
            constant integer signed_sum = SInt(x) + SInt(y) + UInt(carry_in);
            constant bits(N) result = unsigned_sum<N-1:0>; // same value as signed_sum<N-1:0>
            constant bit n = result<N-1>;
            constant bit z = if IsZero(result) then '1' else '0';
            constant bit c = if UInt(result) == unsigned_sum then '0' else '1';
            constant bit v = if SInt(result) == signed_sum then '0' else '1';
            return (result, n:z:c:v);
                 */
        todo!()
    }

    fn translate_operand(&mut self, operand: &bad64::Operand) -> Value {
        use bad64::{Imm, Operand};

        match operand {
            Operand::Reg {
                ref reg,
                arrspec: None,
            } => self.reg_to_value(reg),
            Operand::MemPreIdx { ref reg, imm } => {
                let reg_val = self.reg_to_value(reg);
                match imm {
                    Imm::Unsigned(imm) => {
                        let imm_value = self
                            .builder
                            .ins()
                            .iconst(self.int, i64::try_from(*imm).unwrap());
                        let value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, value);
                        value
                    }
                    Imm::Signed(imm) => {
                        let imm_value = self.builder.ins().iconst(self.int, *imm);
                        let (value, _overflow_flag) =
                            self.builder.ins().sadd_overflow(reg_val, imm_value);
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, value);
                        value
                    }
                }
            }
            Operand::MemPostIdxImm { ref reg, imm } => {
                let reg_val = self.reg_to_value(reg);
                match imm {
                    Imm::Unsigned(imm) => {
                        let imm_value = self
                            .builder
                            .ins()
                            .iconst(self.int, i64::try_from(*imm).unwrap());
                        let post_value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, post_value);
                    }
                    Imm::Signed(imm) => {
                        let imm_value = self.builder.ins().iconst(self.int, *imm);
                        let (post_value, _overflow_flag) =
                            self.builder.ins().sadd_overflow(reg_val, imm_value);
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, post_value);
                    }
                }
                reg_val
            }
            Operand::Imm64 { imm, shift } => {
                let const_value = match imm {
                    Imm::Unsigned(imm) => self
                        .builder
                        .ins()
                        .iconst(self.int, i64::try_from(*imm).unwrap()),
                    Imm::Signed(imm) => self.builder.ins().iconst(self.int, *imm),
                };
                match shift {
                    None => const_value,
                    Some(bad64::Shift::LSL(lsl)) => {
                        let lsl = self.builder.ins().iconst(self.int, i64::from(*lsl));
                        self.builder.ins().ishl(const_value, lsl)
                    }
                    other => unimplemented!("unimplemented shift {other:?}"),
                }
            }
            Operand::Imm32 { imm, shift } => {
                let const_value = match imm {
                    Imm::Unsigned(imm) => self.builder.ins().iconst(self.int, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iconst(self.int, *imm),
                };
                match shift {
                    None => const_value,
                    Some(bad64::Shift::LSL(lsl)) => {
                        let lsl = self.builder.ins().iconst(self.int, i64::from(*lsl));
                        self.builder.ins().ishl(const_value, lsl)
                    }
                    other => unimplemented!("unimplemented shift {other:?}"),
                }
            }
            Operand::MemOffset {
                reg,
                offset,
                mul_vl: false,
                arrspec: None,
            } => {
                let reg_val = self.reg_to_value(reg);
                match offset {
                    Imm::Unsigned(imm) => {
                        let imm_value = self
                            .builder
                            .ins()
                            .iconst(self.int, i64::try_from(*imm).unwrap());
                        let value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        value
                    }
                    Imm::Signed(imm) => {
                        let imm_value = self.builder.ins().iconst(self.int, *imm);
                        let (value, _overflow_flag) =
                            self.builder.ins().sadd_overflow(reg_val, imm_value);
                        value
                    }
                }
            }
            Operand::Label(Imm::Unsigned(imm)) => self.builder.ins().iconst(self.int, *imm as i64),
            Operand::Label(Imm::Signed(imm)) => self.builder.ins().iconst(self.int, *imm),
            Operand::ImplSpec { o0, o1, cm, cn, o2 } => {
                self.translate_o0_op1_CRn_CRm_op2(*o0, *o1, *cm, *cn, *o2)
            }
            Operand::SysReg(reg) => {
                let var = *self.sysreg_to_var(reg);
                self.builder.use_var(var)
            }
            other => unimplemented!("unexpected rhs in translate_operand: {:?}", other),
        }
    }

    #[inline]
    fn sysreg_to_var(&mut self, reg: &bad64::SysReg) -> &Variable {
        self.sys_registers.get(reg).unwrap_or_else(|| {
            unimplemented!("unimplemented sysreg {reg:?}");
        })
    }

    #[inline]
    fn reg_to_var(&mut self, reg: &bad64::Reg, write: bool) -> &Variable {
        use bad64::Reg;

        let reg_64 = match reg {
            Reg::W0 => Reg::X0,
            Reg::W1 => Reg::X1,
            Reg::W2 => Reg::X2,
            Reg::W3 => Reg::X3,
            Reg::W4 => Reg::X4,
            Reg::W5 => Reg::X5,
            Reg::W6 => Reg::X6,
            Reg::W7 => Reg::X7,
            Reg::W8 => Reg::X8,
            Reg::W9 => Reg::X9,
            Reg::W10 => Reg::X10,
            Reg::W11 => Reg::X11,
            Reg::W12 => Reg::X12,
            Reg::W13 => Reg::X13,
            Reg::W14 => Reg::X14,
            Reg::W15 => Reg::X15,
            Reg::W16 => Reg::X16,
            Reg::W17 => Reg::X17,
            Reg::W18 => Reg::X18,
            Reg::W19 => Reg::X19,
            Reg::W20 => Reg::X20,
            Reg::W21 => Reg::X21,
            Reg::W22 => Reg::X22,
            Reg::W23 => Reg::X23,
            Reg::W24 => Reg::X24,
            Reg::W25 => Reg::X25,
            Reg::W26 => Reg::X26,
            Reg::W27 => Reg::X27,
            Reg::W28 => Reg::X28,
            Reg::W29 => Reg::X29,
            Reg::W30 => Reg::X30,
            Reg::WSP => Reg::SP,
            Reg::WZR => return &self.registers[&Reg::XZR],
            _ => {
                return &self.registers[reg];
            }
        };
        if write {
            // Writes to W registers set the higher 32 bits of the X register to zero. So,
            // writing 0xFFFFFFFF into W0 sets X0 to 0x00000000FFFFFFFF.
            let mask = self.builder.ins().iconst(self.int, 0xffff_ffff);
            let unmasked_value = self.builder.use_var(self.registers[&reg_64]);
            let masked_value = self.builder.ins().band(unmasked_value, mask);
            self.builder.def_var(self.registers[&reg_64], masked_value);
        }
        &self.registers[&reg_64]
    }

    #[inline]
    fn reg_to_value(&mut self, reg: &bad64::Reg) -> Value {
        use bad64::Reg;

        let reg_64 = match reg {
            Reg::W0 => Reg::X0,
            Reg::W1 => Reg::X1,
            Reg::W2 => Reg::X2,
            Reg::W3 => Reg::X3,
            Reg::W4 => Reg::X4,
            Reg::W5 => Reg::X5,
            Reg::W6 => Reg::X6,
            Reg::W7 => Reg::X7,
            Reg::W8 => Reg::X8,
            Reg::W9 => Reg::X9,
            Reg::W10 => Reg::X10,
            Reg::W11 => Reg::X11,
            Reg::W12 => Reg::X12,
            Reg::W13 => Reg::X13,
            Reg::W14 => Reg::X14,
            Reg::W15 => Reg::X15,
            Reg::W16 => Reg::X16,
            Reg::W17 => Reg::X17,
            Reg::W18 => Reg::X18,
            Reg::W19 => Reg::X19,
            Reg::W20 => Reg::X20,
            Reg::W21 => Reg::X21,
            Reg::W22 => Reg::X22,
            Reg::W23 => Reg::X23,
            Reg::W24 => Reg::X24,
            Reg::W25 => Reg::X25,
            Reg::W26 => Reg::X26,
            Reg::W27 => Reg::X27,
            Reg::W28 => Reg::X28,
            Reg::W29 => Reg::X29,
            Reg::W30 => Reg::X30,
            Reg::WSP => Reg::SP,
            Reg::XZR | Reg::WZR => {
                return self.builder.ins().iconst(self.int, 0);
            }
            _ => {
                let var = &self.registers[reg];
                return self.builder.use_var(*var);
            }
        };
        // Reads from W registers ignore the higher 32 bits of the corresponding X
        // register and leave them unchanged.
        let mask = self.builder.ins().iconst(self.int, 0xffff_ffff);
        let unmasked_value = self.builder.use_var(self.registers[&reg_64]);
        let masked_value = self.builder.ins().band(unmasked_value, mask);
        masked_value
    }

    fn translate_instruction(
        &mut self,
        instruction: bad64::Instruction,
    ) -> ControlFlow<Option<Value>> {
        use bad64::Op;

        let op = instruction.op();
        match op {
            Op::NOP => {}
            // Special registers
            Op::MSR => {
                // TODO: AArch64.CheckSystemAccess
                let target = match instruction.operands()[0] {
                    bad64::Operand::SysReg(ref sysreg) => *self.sysreg_to_var(sysreg),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let value = self.translate_operand(&instruction.operands()[1]);
                self.builder.def_var(target, value);
            }
            Op::MRS => {
                // TODO: AArch64.CheckSystemAccess
                // Move System register to general-purpose register
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let sys_reg_value = self.translate_operand(&instruction.operands()[1]);
                self.builder.def_var(target, sys_reg_value);
            }
            // Memory-ops
            Op::ADRP => {
                // Form PC-relative address to 4KB page
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let imm_value = self.translate_operand(&instruction.operands()[1]);
                let twelve = self.builder.ins().iconst(self.int, 12);
                let shifted_imm_value = self.builder.ins().ishl(imm_value, twelve);
                let pc = self
                    .builder
                    .ins()
                    .iconst(self.int, self.mem_start + instruction.address() as i64);
                let (value, _overflow_flag) =
                    self.builder.ins().sadd_overflow(pc, shifted_imm_value);
                self.builder.def_var(target, value);
            }
            Op::ADR => {
                // Form PC-relative address
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let imm_value = self.translate_operand(&instruction.operands()[1]);
                let pc = self
                    .builder
                    .ins()
                    .iconst(self.int, self.mem_start + instruction.address() as i64);
                let (value, _overflow_flag) = self.builder.ins().sadd_overflow(pc, imm_value);
                self.builder.def_var(target, value);
            }
            Op::STR => {
                let value = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => self.reg_to_value(reg),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let target = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(self.int, self.mem_start);
                let (target, _overflow_flag) = self.builder.ins().sadd_overflow(mem_start, target);
                self.builder.ins().store(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    Offset32::new(0),
                );
            }
            Op::LDR => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(self.int, self.mem_start);
                let (source_address, _overflow_flag) =
                    self.builder.ins().sadd_overflow(mem_start, source_address);
                let value = self.builder.ins().load(
                    cranelift::prelude::Type::int(64).unwrap(),
                    MemFlags::new(),
                    source_address,
                    Offset32::new(0),
                );
                self.builder.def_var(target, value);
            }
            // Moves
            Op::MOV => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let value = self.translate_operand(&instruction.operands()[1]);
                self.builder.def_var(target, value);
            }
            Op::MOVK => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let (imm_value, shift_mask): (Value, u64) = match &instruction.operands()[1] {
                    bad64::Operand::Imm64 { imm, shift } => {
                        let const_value = match imm {
                            bad64::Imm::Unsigned(imm) => self
                                .builder
                                .ins()
                                .iconst(self.int, i64::try_from(*imm).unwrap()),
                            bad64::Imm::Signed(imm) => self.builder.ins().iconst(self.int, *imm),
                        };
                        match shift {
                            None => (const_value, !0xf),
                            Some(bad64::Shift::LSL(lsl)) => {
                                let lsl_value =
                                    self.builder.ins().iconst(self.int, i64::from(*lsl));
                                let const_value = self.builder.ins().ishl(const_value, lsl_value);
                                let shift_mask = match lsl {
                                    16 => !0xf0,
                                    32 => !0xf00,
                                    48 => !0xf000,
                                    other => panic!("other shift {other}"),
                                };
                                (const_value, shift_mask)
                            }
                            other => unimplemented!("unimplemented shift {other:?}"),
                        }
                    }
                    other => panic!("other: {:?}", other),
                };
                let mask = self.builder.ins().iconst(self.int, shift_mask as i64);
                let unmasked_value = self.builder.use_var(target);
                let masked_value = self.builder.ins().band(unmasked_value, mask);
                let value = self.builder.ins().bor(masked_value, imm_value);
                self.builder.def_var(target, value);
            }
            Op::MOVZ => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let imm_value = self.translate_operand(&instruction.operands()[1]);
                self.builder.def_var(target, imm_value);
            }
            // Int-ops
            Op::ADD => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let (value, _ignore_overflow) = self.builder.ins().sadd_overflow(a, b);
                self.builder.def_var(target, value);
            }
            Op::SUB => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in load: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let (value, _ignore_overflow) = self.builder.ins().usub_overflow(a, b);
                self.builder.def_var(target, value);
            }
            Op::SUBS => {
                // FIXME: update NZCV flags
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in load: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let (value, _ignore_overflow) = self.builder.ins().usub_overflow(a, b);
                self.builder.def_var(target, value);
            }
            Op::MUL => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in load: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().imul(a, b);
                self.builder.def_var(target, value);
            }
            Op::SDIV => {
                /*
                constant bits(datasize) operand1 = X[n, datasize];
                constant bits(datasize) operand2 = X[m, datasize];
                constant integer dividend = SInt(operand1);
                constant integer divisor  = SInt(operand2);
                integer result;
                if divisor == 0 then
                result = 0;
                elsif (dividend < 0) == (divisor < 0) then
                result = Abs(dividend) DIV Abs(divisor);    // same signs - positive result
                else
                result = -(Abs(dividend) DIV Abs(divisor)); // different signs - negative result
                X[d, datasize] = result<datasize-1:0>;
                */
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in load: {:?}", other),
                };
                let dividend = self.translate_operand(&instruction.operands()[1]);
                let divisor = self.translate_operand(&instruction.operands()[2]);
                // if divisor == 0 then
                // result = 0;
                let zero = self.reg_to_value(&bad64::Reg::XZR);
                let first_condition_value =
                    self.builder
                        .ins()
                        .icmp(cranelift::prelude::IntCC::Equal, divisor, zero);

                let zero_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, self.int);

                // Test the if condition and conditionally branch.
                self.builder
                    .ins()
                    .brif(first_condition_value, zero_block, &[], else_block, &[]);

                self.builder.switch_to_block(zero_block);
                self.builder.seal_block(zero_block);
                // Jump to the merge block, passing it the block return value.
                self.builder.ins().jump(merge_block, &[zero]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let else_return = self.builder.ins().sdiv(dividend, divisor);
                // Jump to the merge block, passing it the block return value.
                self.builder.ins().jump(merge_block, &[else_return]);

                // Switch to the merge block for subsequent statements.
                self.builder.switch_to_block(merge_block);

                // We've now seen all the predecessors of the merge block.
                self.builder.seal_block(merge_block);

                // Read the value of the if-else by reading the merge block
                // parameter.
                let phi = self.builder.block_params(merge_block)[0];

                self.builder.def_var(target, phi);
            }
            // Branches
            Op::B => {
                // This instruction branches unconditionally to a label at a PC-relative offset,
                // with a hint that this is not a subroutine call or return.
                // constant boolean branch_conditional = FALSE;
                // BranchTo(PC64 + offset, BranchType_DIR, branch_conditional);
                let label = match instruction.operands()[0] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!("unexpected branch address in {op:?}: {:?}", other),
                };
                let pc = self
                    .builder
                    .ins()
                    .iconst(self.int, instruction.address() as i64);
                self.builder.ins().store(
                    MemFlags::trusted().with_vmctx(),
                    pc,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, prev_pc) as i32,
                );
                let next_pc = self.builder.ins().iconst(self.int, label as i64);
                self.builder.ins().store(
                    MemFlags::trusted().with_vmctx(),
                    next_pc,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, pc) as i32,
                );
                return ControlFlow::Break(Some(next_pc));
            }
            Op::BR => {
                // This instruction branches unconditionally to an address in a register, with a
                // hint that this is not a subroutine return.
                //
                // constant bits(64) target = X[n, 64];
                // Value in BTypeNext will be used to set PSTATE.BTYPE
                // if InGuardedPage then
                //     if n == 16 || n == 17 then
                //         BTypeNext = '01';
                //     else
                //         BTypeNext = '11';
                // else
                //     BTypeNext = '01';

                // constant boolean branch_conditional = FALSE;
                // BranchTo(target, BranchType_INDIR, branch_conditional);
                let next_pc = self.translate_operand(&instruction.operands()[0]);
                let pc = self
                    .builder
                    .ins()
                    .iconst(self.int, instruction.address() as i64);
                self.builder.ins().store(
                    MemFlags::trusted().with_vmctx(),
                    pc,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, prev_pc) as i32,
                );
                self.builder.ins().store(
                    MemFlags::trusted().with_vmctx(),
                    next_pc,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, pc) as i32,
                );
                return ControlFlow::Break(Some(next_pc));
            }
            Op::RET => {
                // FIXME

                let bool_type =
                    cranelift::prelude::Type::int(8).expect("Could not create bool type");
                let true_value = self.builder.ins().iconst(bool_type, 1);
                self.builder.ins().store(
                    MemFlags::trusted().with_vmctx(),
                    true_value,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, halted) as i32,
                );
                // let next_pc = self
                //     .builder
                //     .ins()
                //     .iconst(self.int, instruction.address() as i64);
                // return ControlFlow::Break(next_pc);
            }
            // Compares
            Op::CBNZ => {
                /*
                 * constant boolean branch_conditional = TRUE;
                 * constant bits(datasize) operand1 = X[t, datasize];
                 * if !IsZero(operand1) then
                 *     BranchTo(PC64 + offset, BranchType_DIR, branch_conditional);
                 * else
                 *     BranchNotTaken(BranchType_DIR, branch_conditional);
                 */
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let label = match instruction.operands()[1] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!("unexpected branch address in {op:?}: {:?}", other),
                };
                let branch_not_taken_block = self.builder.create_block();
                let branch_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                self.builder.append_block_param(merge_block, self.int);
                let zero = self.reg_to_value(&bad64::Reg::XZR);
                let is_zero_value =
                    self.builder
                        .ins()
                        .icmp(cranelift::prelude::IntCC::Equal, operand1, zero);
                let is_zero_value = self.builder.ins().sextend(self.int, is_zero_value);
                self.builder.ins().brif(
                    is_zero_value,
                    branch_not_taken_block,
                    &[],
                    branch_block,
                    &[],
                );
                self.builder.switch_to_block(branch_not_taken_block);
                self.builder.seal_block(branch_not_taken_block);
                // Jump to the merge block, passing it the block return value.
                self.builder.ins().jump(merge_block, &[is_zero_value]);
                self.builder.switch_to_block(branch_block);
                self.builder.seal_block(branch_block);
                let label_value = self.builder.ins().iconst(self.int, label as i64);
                self.emit_jump(label_value);
                // Switch to the merge block for subsequent statements.
                self.builder.switch_to_block(merge_block);

                // We've now seen all the predecessors of the merge block.
                self.builder.seal_block(merge_block);
            }
            // Bit-ops
            Op::BFI => {
                // Bitfield insert
                // This instruction copies a bitfield of <width> bits from the least significant
                // bits of the source register to bit position <lsb> of the destination
                // register, leaving the other destination bits unchanged.
                /*
                 * if sf == '1' && N != '1' then EndOfDecode(Decode_UNDEF);
                    if sf == '0' && (N != '0' || immr<5> != '0' || imms<5> != '0') then EndOfDecode(Decode_UNDEF);

                    constant integer d = UInt(Rd);
                    constant integer n = UInt(Rn);
                    constant integer datasize = 32 << UInt(sf);
                    constant integer s = UInt(imms);
                    constant integer r = UInt(immr);

                    bits(datasize) wmask;
                    bits(datasize) tmask;
                    (wmask, tmask) = DecodeBitMasks(N, imms, immr, FALSE, datasize);
                   constant bits(datasize) dst = X[d, datasize];
                   constant bits(datasize) src = X[n, datasize];

                // Perform bitfield move on low bits
                constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND wmask);

                // Combine extension bits and result bits
                X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
                 */
                let dst = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let src = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, false),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                // TODO...
            }
            Op::ORR => {
                // Bitwise OR (immediate)
                // This instruction performs a bitwise (inclusive) OR of a register value and an
                // immediate value, and writes the result to the destination register.
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().bor(a, b);
                self.builder.def_var(target, value);
            }
            Op::LSL => {
                // Logical shift left
                // This instruction shifts a register value left by an immediate number of bits,
                // shifting in zeros, and writes the result to the destination register
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().ishl(a, b);
                self.builder.def_var(target, value);
            }
            Op::AND => todo!(),

            // rest
            Op::ABS => todo!(),
            Op::ADC => todo!(),
            Op::ADCLB => todo!(),
            Op::ADCLT => todo!(),
            Op::ADCS => todo!(),
            Op::ADDG => todo!(),
            Op::ADDHA => todo!(),
            Op::ADDHN => todo!(),
            Op::ADDHN2 => todo!(),
            Op::ADDHNB => todo!(),
            Op::ADDHNT => todo!(),
            Op::ADDP => todo!(),
            Op::ADDPL => todo!(),
            Op::ADDS => todo!(),
            Op::ADDV => todo!(),
            Op::ADDVA => todo!(),
            Op::ADDVL => todo!(),
            Op::AESD => todo!(),
            Op::AESE => todo!(),
            Op::AESIMC => todo!(),
            Op::AESMC => todo!(),
            Op::ANDS => todo!(),
            Op::ANDV => todo!(),
            Op::ASR => todo!(),
            Op::ASRD => todo!(),
            Op::ASRR => todo!(),
            Op::ASRV => todo!(),
            Op::AT => todo!(),
            Op::AUTDA => todo!(),
            Op::AUTDB => todo!(),
            Op::AUTDZA => todo!(),
            Op::AUTDZB => todo!(),
            Op::AUTIA => todo!(),
            Op::AUTIA1716 => todo!(),
            Op::AUTIASP => todo!(),
            Op::AUTIAZ => todo!(),
            Op::AUTIB => todo!(),
            Op::AUTIB1716 => todo!(),
            Op::AUTIBSP => todo!(),
            Op::AUTIBZ => todo!(),
            Op::AUTIZA => todo!(),
            Op::AUTIZB => todo!(),
            Op::AXFLAG => todo!(),
            Op::BCAX => todo!(),
            Op::BDEP => todo!(),
            Op::BEXT => todo!(),
            Op::BFC => todo!(),
            Op::BFCVT => todo!(),
            Op::BFCVTN => todo!(),
            Op::BFCVTN2 => todo!(),
            Op::BFCVTNT => todo!(),
            Op::BFDOT => todo!(),
            Op::BFM => todo!(),
            Op::BFMLAL => todo!(),
            Op::BFMLALB => todo!(),
            Op::BFMLALT => todo!(),
            Op::BFMMLA => todo!(),
            Op::BFMOPA => todo!(),
            Op::BFMOPS => todo!(),
            Op::BFXIL => todo!(),
            Op::BGRP => todo!(),
            Op::BIC => todo!(),
            Op::BICS => todo!(),
            Op::BIF => todo!(),
            Op::BIT => todo!(),
            Op::BL => todo!(),
            Op::BLR => todo!(),
            Op::BLRAA => todo!(),
            Op::BLRAAZ => todo!(),
            Op::BLRAB => todo!(),
            Op::BLRABZ => todo!(),
            Op::BRAA => todo!(),
            Op::BRAAZ => todo!(),
            Op::BRAB => todo!(),
            Op::BRABZ => todo!(),
            Op::BRK => todo!(),
            Op::BRKA => todo!(),
            Op::BRKAS => todo!(),
            Op::BRKB => todo!(),
            Op::BRKBS => todo!(),
            Op::BRKN => todo!(),
            Op::BRKNS => todo!(),
            Op::BRKPA => todo!(),
            Op::BRKPAS => todo!(),
            Op::BRKPB => todo!(),
            Op::BRKPBS => todo!(),
            Op::BSL => todo!(),
            Op::BSL1N => todo!(),
            Op::BSL2N => todo!(),
            Op::BTI => todo!(),
            Op::B_AL => todo!(),
            Op::B_CC => todo!(),
            Op::B_CS => todo!(),
            Op::B_EQ => todo!(),
            Op::B_GE => todo!(),
            Op::B_GT => todo!(),
            Op::B_HI => todo!(),
            Op::B_LE => todo!(),
            Op::B_LS => todo!(),
            Op::B_LT => todo!(),
            Op::B_MI => todo!(),
            Op::B_NE => todo!(),
            Op::B_NV => todo!(),
            Op::B_PL => todo!(),
            Op::B_VC => todo!(),
            Op::B_VS => todo!(),
            Op::CADD => todo!(),
            Op::CAS => todo!(),
            Op::CASA => todo!(),
            Op::CASAB => todo!(),
            Op::CASAH => todo!(),
            Op::CASAL => todo!(),
            Op::CASALB => todo!(),
            Op::CASALH => todo!(),
            Op::CASB => todo!(),
            Op::CASH => todo!(),
            Op::CASL => todo!(),
            Op::CASLB => todo!(),
            Op::CASLH => todo!(),
            Op::CASP => todo!(),
            Op::CASPA => todo!(),
            Op::CASPAL => todo!(),
            Op::CASPL => todo!(),
            Op::CBZ => todo!(),
            Op::CCMN => todo!(),
            Op::CCMP => todo!(),
            Op::CDOT => todo!(),
            Op::CFINV => todo!(),
            Op::CFP => todo!(),
            Op::CINC => todo!(),
            Op::CINV => todo!(),
            Op::CLASTA => todo!(),
            Op::CLASTB => todo!(),
            Op::CLREX => todo!(),
            Op::CLS => todo!(),
            Op::CLZ => todo!(),
            Op::CMEQ => todo!(),
            Op::CMGE => todo!(),
            Op::CMGT => todo!(),
            Op::CMHI => todo!(),
            Op::CMHS => todo!(),
            Op::CMLA => todo!(),
            Op::CMLE => todo!(),
            Op::CMLT => todo!(),
            Op::CMN => todo!(),
            Op::CMP => {
                self.translate_cmp_64(&instruction);
                /*
                                 * constant bits(datasize) operand1 = if n == 31 then SP[datasize] else X[n, datasize];
                constant bits(datasize) operand2 = NOT(ExtendReg(m, extend_type, shift, datasize));
                bits(datasize) result;
                bits(4) nzcv;

                (result, nzcv) = AddWithCarry(operand1, operand2, '1');

                X[d, datasize] = result;
                PSTATE.<N,Z,C,V> = nzcv;
                                */
                // FIXME
            }
            Op::CMPEQ => todo!(),
            Op::CMPGE => todo!(),
            Op::CMPGT => todo!(),
            Op::CMPHI => todo!(),
            Op::CMPHS => todo!(),
            Op::CMPLE => todo!(),
            Op::CMPLO => todo!(),
            Op::CMPLS => todo!(),
            Op::CMPLT => todo!(),
            Op::CMPNE => todo!(),
            Op::CMPP => todo!(),
            Op::CMTST => todo!(),
            Op::CNEG => todo!(),
            Op::CNOT => todo!(),
            Op::CNT => todo!(),
            Op::CNTB => todo!(),
            Op::CNTD => todo!(),
            Op::CNTH => todo!(),
            Op::CNTP => todo!(),
            Op::CNTW => todo!(),
            Op::COMPACT => todo!(),
            Op::CPP => todo!(),
            Op::CPY => todo!(),
            Op::CRC32B => todo!(),
            Op::CRC32CB => todo!(),
            Op::CRC32CH => todo!(),
            Op::CRC32CW => todo!(),
            Op::CRC32CX => todo!(),
            Op::CRC32H => todo!(),
            Op::CRC32W => todo!(),
            Op::CRC32X => todo!(),
            Op::CSDB => todo!(),
            Op::CSEL => {
                todo!()
            }
            Op::CSET => todo!(),
            Op::CSETM => todo!(),
            Op::CSINC => todo!(),
            Op::CSINV => todo!(),
            Op::CSNEG => todo!(),
            Op::CTERMEQ => todo!(),
            Op::CTERMNE => todo!(),
            Op::DC => todo!(),
            Op::DCPS1 => todo!(),
            Op::DCPS2 => todo!(),
            Op::DCPS3 => todo!(),
            Op::DECB => todo!(),
            Op::DECD => todo!(),
            Op::DECH => todo!(),
            Op::DECP => todo!(),
            Op::DECW => todo!(),
            Op::DGH => todo!(),
            Op::DMB => todo!(),
            Op::DRPS => todo!(),
            Op::DSB => {
                // Data synchronization barrier
            }
            Op::DUP => todo!(),
            Op::DUPM => todo!(),
            Op::DVP => todo!(),
            Op::EON => todo!(),
            Op::EOR => todo!(),
            Op::EOR3 => todo!(),
            Op::EORBT => todo!(),
            Op::EORS => todo!(),
            Op::EORTB => todo!(),
            Op::EORV => todo!(),
            Op::ERET => {
                // FIXME

                let bool_type =
                    cranelift::prelude::Type::int(8).expect("Could not create bool type");
                let true_value = self.builder.ins().iconst(bool_type, 1);
                self.builder.ins().store(
                    MemFlags::trusted().with_vmctx(),
                    true_value,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, halted) as i32,
                );
            }
            Op::ERETAA => todo!(),
            Op::ERETAB => todo!(),
            Op::ESB => todo!(),
            Op::EXT => todo!(),
            Op::EXTR => todo!(),
            Op::FABD => todo!(),
            Op::FABS => todo!(),
            Op::FACGE => todo!(),
            Op::FACGT => todo!(),
            Op::FACLE => todo!(),
            Op::FACLT => todo!(),
            Op::FADD => todo!(),
            Op::FADDA => todo!(),
            Op::FADDP => todo!(),
            Op::FADDV => todo!(),
            Op::FCADD => todo!(),
            Op::FCCMP => todo!(),
            Op::FCCMPE => todo!(),
            Op::FCMEQ => todo!(),
            Op::FCMGE => todo!(),
            Op::FCMGT => todo!(),
            Op::FCMLA => todo!(),
            Op::FCMLE => todo!(),
            Op::FCMLT => todo!(),
            Op::FCMNE => todo!(),
            Op::FCMP => todo!(),
            Op::FCMPE => todo!(),
            Op::FCMUO => todo!(),
            Op::FCPY => todo!(),
            Op::FCSEL => todo!(),
            Op::FCVT => todo!(),
            Op::FCVTAS => todo!(),
            Op::FCVTAU => todo!(),
            Op::FCVTL => todo!(),
            Op::FCVTL2 => todo!(),
            Op::FCVTLT => todo!(),
            Op::FCVTMS => todo!(),
            Op::FCVTMU => todo!(),
            Op::FCVTN => todo!(),
            Op::FCVTN2 => todo!(),
            Op::FCVTNS => todo!(),
            Op::FCVTNT => todo!(),
            Op::FCVTNU => todo!(),
            Op::FCVTPS => todo!(),
            Op::FCVTPU => todo!(),
            Op::FCVTX => todo!(),
            Op::FCVTXN => todo!(),
            Op::FCVTXN2 => todo!(),
            Op::FCVTXNT => todo!(),
            Op::FCVTZS => todo!(),
            Op::FCVTZU => todo!(),
            Op::FDIV => todo!(),
            Op::FDIVR => todo!(),
            Op::FDUP => todo!(),
            Op::FEXPA => todo!(),
            Op::FJCVTZS => todo!(),
            Op::FLOGB => todo!(),
            Op::FMAD => todo!(),
            Op::FMADD => todo!(),
            Op::FMAX => todo!(),
            Op::FMAXNM => todo!(),
            Op::FMAXNMP => todo!(),
            Op::FMAXNMV => todo!(),
            Op::FMAXP => todo!(),
            Op::FMAXV => todo!(),
            Op::FMIN => todo!(),
            Op::FMINNM => todo!(),
            Op::FMINNMP => todo!(),
            Op::FMINNMV => todo!(),
            Op::FMINP => todo!(),
            Op::FMINV => todo!(),
            Op::FMLA => todo!(),
            Op::FMLAL => todo!(),
            Op::FMLAL2 => todo!(),
            Op::FMLALB => todo!(),
            Op::FMLALT => todo!(),
            Op::FMLS => todo!(),
            Op::FMLSL => todo!(),
            Op::FMLSL2 => todo!(),
            Op::FMLSLB => todo!(),
            Op::FMLSLT => todo!(),
            Op::FMMLA => todo!(),
            Op::FMOPA => todo!(),
            Op::FMOPS => todo!(),
            Op::FMOV => todo!(),
            Op::FMSB => todo!(),
            Op::FMSUB => todo!(),
            Op::FMUL => todo!(),
            Op::FMULX => todo!(),
            Op::FNEG => todo!(),
            Op::FNMAD => todo!(),
            Op::FNMADD => todo!(),
            Op::FNMLA => todo!(),
            Op::FNMLS => todo!(),
            Op::FNMSB => todo!(),
            Op::FNMSUB => todo!(),
            Op::FNMUL => todo!(),
            Op::FRECPE => todo!(),
            Op::FRECPS => todo!(),
            Op::FRECPX => todo!(),
            Op::FRINT32X => todo!(),
            Op::FRINT32Z => todo!(),
            Op::FRINT64X => todo!(),
            Op::FRINT64Z => todo!(),
            Op::FRINTA => todo!(),
            Op::FRINTI => todo!(),
            Op::FRINTM => todo!(),
            Op::FRINTN => todo!(),
            Op::FRINTP => todo!(),
            Op::FRINTX => todo!(),
            Op::FRINTZ => todo!(),
            Op::FRSQRTE => todo!(),
            Op::FRSQRTS => todo!(),
            Op::FSCALE => todo!(),
            Op::FSQRT => todo!(),
            Op::FSUB => todo!(),
            Op::FSUBR => todo!(),
            Op::FTMAD => todo!(),
            Op::FTSMUL => todo!(),
            Op::FTSSEL => todo!(),
            Op::GMI => todo!(),
            Op::HINT => todo!(),
            Op::HISTCNT => todo!(),
            Op::HISTSEG => todo!(),
            Op::HLT => todo!(),
            Op::HVC => todo!(),
            Op::IC => {
                // Instruction cache operation
            }
            Op::INCB => todo!(),
            Op::INCD => todo!(),
            Op::INCH => todo!(),
            Op::INCP => todo!(),
            Op::INCW => todo!(),
            Op::INDEX => todo!(),
            Op::INS => todo!(),
            Op::INSR => todo!(),
            Op::IRG => todo!(),
            Op::ISB => {
                // Instruction synchronization barrier
            }
            Op::LASTA => todo!(),
            Op::LASTB => todo!(),
            Op::LD1 => todo!(),
            Op::LD1B => todo!(),
            Op::LD1D => todo!(),
            Op::LD1H => todo!(),
            Op::LD1Q => todo!(),
            Op::LD1R => todo!(),
            Op::LD1RB => todo!(),
            Op::LD1RD => todo!(),
            Op::LD1RH => todo!(),
            Op::LD1ROB => todo!(),
            Op::LD1ROD => todo!(),
            Op::LD1ROH => todo!(),
            Op::LD1ROW => todo!(),
            Op::LD1RQB => todo!(),
            Op::LD1RQD => todo!(),
            Op::LD1RQH => todo!(),
            Op::LD1RQW => todo!(),
            Op::LD1RSB => todo!(),
            Op::LD1RSH => todo!(),
            Op::LD1RSW => todo!(),
            Op::LD1RW => todo!(),
            Op::LD1SB => todo!(),
            Op::LD1SH => todo!(),
            Op::LD1SW => todo!(),
            Op::LD1W => todo!(),
            Op::LD2 => todo!(),
            Op::LD2B => todo!(),
            Op::LD2D => todo!(),
            Op::LD2H => todo!(),
            Op::LD2R => todo!(),
            Op::LD2W => todo!(),
            Op::LD3 => todo!(),
            Op::LD3B => todo!(),
            Op::LD3D => todo!(),
            Op::LD3H => todo!(),
            Op::LD3R => todo!(),
            Op::LD3W => todo!(),
            Op::LD4 => todo!(),
            Op::LD4B => todo!(),
            Op::LD4D => todo!(),
            Op::LD4H => todo!(),
            Op::LD4R => todo!(),
            Op::LD4W => todo!(),
            Op::LD64B => todo!(),
            Op::LDADD => todo!(),
            Op::LDADDA => todo!(),
            Op::LDADDAB => todo!(),
            Op::LDADDAH => todo!(),
            Op::LDADDAL => todo!(),
            Op::LDADDALB => todo!(),
            Op::LDADDALH => todo!(),
            Op::LDADDB => todo!(),
            Op::LDADDH => todo!(),
            Op::LDADDL => todo!(),
            Op::LDADDLB => todo!(),
            Op::LDADDLH => todo!(),
            Op::LDAPR => todo!(),
            Op::LDAPRB => todo!(),
            Op::LDAPRH => todo!(),
            Op::LDAPUR => todo!(),
            Op::LDAPURB => todo!(),
            Op::LDAPURH => todo!(),
            Op::LDAPURSB => todo!(),
            Op::LDAPURSH => todo!(),
            Op::LDAPURSW => todo!(),
            Op::LDAR => todo!(),
            Op::LDARB => todo!(),
            Op::LDARH => todo!(),
            Op::LDAXP => todo!(),
            Op::LDAXR => todo!(),
            Op::LDAXRB => todo!(),
            Op::LDAXRH => todo!(),
            Op::LDCLR => todo!(),
            Op::LDCLRA => todo!(),
            Op::LDCLRAB => todo!(),
            Op::LDCLRAH => todo!(),
            Op::LDCLRAL => todo!(),
            Op::LDCLRALB => todo!(),
            Op::LDCLRALH => todo!(),
            Op::LDCLRB => todo!(),
            Op::LDCLRH => todo!(),
            Op::LDCLRL => todo!(),
            Op::LDCLRLB => todo!(),
            Op::LDCLRLH => todo!(),
            Op::LDEOR => todo!(),
            Op::LDEORA => todo!(),
            Op::LDEORAB => todo!(),
            Op::LDEORAH => todo!(),
            Op::LDEORAL => todo!(),
            Op::LDEORALB => todo!(),
            Op::LDEORALH => todo!(),
            Op::LDEORB => todo!(),
            Op::LDEORH => todo!(),
            Op::LDEORL => todo!(),
            Op::LDEORLB => todo!(),
            Op::LDEORLH => todo!(),
            Op::LDFF1B => todo!(),
            Op::LDFF1D => todo!(),
            Op::LDFF1H => todo!(),
            Op::LDFF1SB => todo!(),
            Op::LDFF1SH => todo!(),
            Op::LDFF1SW => todo!(),
            Op::LDFF1W => todo!(),
            Op::LDG => todo!(),
            Op::LDGM => todo!(),
            Op::LDLAR => todo!(),
            Op::LDLARB => todo!(),
            Op::LDLARH => todo!(),
            Op::LDNF1B => todo!(),
            Op::LDNF1D => todo!(),
            Op::LDNF1H => todo!(),
            Op::LDNF1SB => todo!(),
            Op::LDNF1SH => todo!(),
            Op::LDNF1SW => todo!(),
            Op::LDNF1W => todo!(),
            Op::LDNP => todo!(),
            Op::LDNT1B => todo!(),
            Op::LDNT1D => todo!(),
            Op::LDNT1H => todo!(),
            Op::LDNT1SB => todo!(),
            Op::LDNT1SH => todo!(),
            Op::LDNT1SW => todo!(),
            Op::LDNT1W => todo!(),
            Op::LDP => todo!(),
            Op::LDPSW => todo!(),
            Op::LDRAA => todo!(),
            Op::LDRAB => todo!(),
            Op::LDRB => todo!(),
            Op::LDRH => todo!(),
            Op::LDRSB => todo!(),
            Op::LDRSH => todo!(),
            Op::LDRSW => todo!(),
            Op::LDSET => todo!(),
            Op::LDSETA => todo!(),
            Op::LDSETAB => todo!(),
            Op::LDSETAH => todo!(),
            Op::LDSETAL => todo!(),
            Op::LDSETALB => todo!(),
            Op::LDSETALH => todo!(),
            Op::LDSETB => todo!(),
            Op::LDSETH => todo!(),
            Op::LDSETL => todo!(),
            Op::LDSETLB => todo!(),
            Op::LDSETLH => todo!(),
            Op::LDSMAX => todo!(),
            Op::LDSMAXA => todo!(),
            Op::LDSMAXAB => todo!(),
            Op::LDSMAXAH => todo!(),
            Op::LDSMAXAL => todo!(),
            Op::LDSMAXALB => todo!(),
            Op::LDSMAXALH => todo!(),
            Op::LDSMAXB => todo!(),
            Op::LDSMAXH => todo!(),
            Op::LDSMAXL => todo!(),
            Op::LDSMAXLB => todo!(),
            Op::LDSMAXLH => todo!(),
            Op::LDSMIN => todo!(),
            Op::LDSMINA => todo!(),
            Op::LDSMINAB => todo!(),
            Op::LDSMINAH => todo!(),
            Op::LDSMINAL => todo!(),
            Op::LDSMINALB => todo!(),
            Op::LDSMINALH => todo!(),
            Op::LDSMINB => todo!(),
            Op::LDSMINH => todo!(),
            Op::LDSMINL => todo!(),
            Op::LDSMINLB => todo!(),
            Op::LDSMINLH => todo!(),
            Op::LDTR => todo!(),
            Op::LDTRB => todo!(),
            Op::LDTRH => todo!(),
            Op::LDTRSB => todo!(),
            Op::LDTRSH => todo!(),
            Op::LDTRSW => todo!(),
            Op::LDUMAX => todo!(),
            Op::LDUMAXA => todo!(),
            Op::LDUMAXAB => todo!(),
            Op::LDUMAXAH => todo!(),
            Op::LDUMAXAL => todo!(),
            Op::LDUMAXALB => todo!(),
            Op::LDUMAXALH => todo!(),
            Op::LDUMAXB => todo!(),
            Op::LDUMAXH => todo!(),
            Op::LDUMAXL => todo!(),
            Op::LDUMAXLB => todo!(),
            Op::LDUMAXLH => todo!(),
            Op::LDUMIN => todo!(),
            Op::LDUMINA => todo!(),
            Op::LDUMINAB => todo!(),
            Op::LDUMINAH => todo!(),
            Op::LDUMINAL => todo!(),
            Op::LDUMINALB => todo!(),
            Op::LDUMINALH => todo!(),
            Op::LDUMINB => todo!(),
            Op::LDUMINH => todo!(),
            Op::LDUMINL => todo!(),
            Op::LDUMINLB => todo!(),
            Op::LDUMINLH => todo!(),
            Op::LDUR => todo!(),
            Op::LDURB => todo!(),
            Op::LDURH => todo!(),
            Op::LDURSB => todo!(),
            Op::LDURSH => todo!(),
            Op::LDURSW => todo!(),
            Op::LDXP => todo!(),
            Op::LDXR => todo!(),
            Op::LDXRB => todo!(),
            Op::LDXRH => todo!(),
            Op::LSLR => todo!(),
            Op::LSLV => todo!(),
            Op::LSR => todo!(),
            Op::LSRR => todo!(),
            Op::LSRV => todo!(),
            Op::MAD => todo!(),
            Op::MADD => todo!(),
            Op::MATCH => todo!(),
            Op::MLA => todo!(),
            Op::MLS => todo!(),
            Op::MNEG => todo!(),
            Op::MOVA => todo!(),
            Op::MOVI => todo!(),
            Op::MOVN => todo!(),
            Op::MOVPRFX => todo!(),
            Op::MOVS => todo!(),
            Op::MSB => todo!(),
            Op::MSUB => todo!(),
            Op::MVN => todo!(),
            Op::MVNI => todo!(),
            Op::NAND => todo!(),
            Op::NANDS => todo!(),
            Op::NBSL => todo!(),
            Op::NEG => todo!(),
            Op::NEGS => todo!(),
            Op::NGC => todo!(),
            Op::NGCS => todo!(),
            Op::NMATCH => todo!(),
            Op::NOR => todo!(),
            Op::NORS => todo!(),
            Op::NOT => todo!(),
            Op::NOTS => todo!(),
            Op::ORN => todo!(),
            Op::ORNS => todo!(),
            Op::ORRS => todo!(),
            Op::ORV => todo!(),
            Op::PACDA => todo!(),
            Op::PACDB => todo!(),
            Op::PACDZA => todo!(),
            Op::PACDZB => todo!(),
            Op::PACGA => todo!(),
            Op::PACIA => todo!(),
            Op::PACIA1716 => todo!(),
            Op::PACIASP => todo!(),
            Op::PACIAZ => todo!(),
            Op::PACIB => todo!(),
            Op::PACIB1716 => todo!(),
            Op::PACIBSP => todo!(),
            Op::PACIBZ => todo!(),
            Op::PACIZA => todo!(),
            Op::PACIZB => todo!(),
            Op::PFALSE => todo!(),
            Op::PFIRST => todo!(),
            Op::PMUL => todo!(),
            Op::PMULL => todo!(),
            Op::PMULL2 => todo!(),
            Op::PMULLB => todo!(),
            Op::PMULLT => todo!(),
            Op::PNEXT => todo!(),
            Op::PRFB => todo!(),
            Op::PRFD => todo!(),
            Op::PRFH => todo!(),
            Op::PRFM => todo!(),
            Op::PRFUM => todo!(),
            Op::PRFW => todo!(),
            Op::PSB => todo!(),
            Op::PSSBB => todo!(),
            Op::PTEST => todo!(),
            Op::PTRUE => todo!(),
            Op::PTRUES => todo!(),
            Op::PUNPKHI => todo!(),
            Op::PUNPKLO => todo!(),
            Op::RADDHN => todo!(),
            Op::RADDHN2 => todo!(),
            Op::RADDHNB => todo!(),
            Op::RADDHNT => todo!(),
            Op::RAX1 => todo!(),
            Op::RBIT => todo!(),
            Op::RDFFR => todo!(),
            Op::RDFFRS => todo!(),
            Op::RDVL => todo!(),
            Op::RETAA => todo!(),
            Op::RETAB => todo!(),
            Op::REV => todo!(),
            Op::REV16 => todo!(),
            Op::REV32 => todo!(),
            Op::REV64 => todo!(),
            Op::REVB => todo!(),
            Op::REVD => todo!(),
            Op::REVH => todo!(),
            Op::REVW => todo!(),
            Op::RMIF => todo!(),
            Op::ROR => todo!(),
            Op::RORV => todo!(),
            Op::RSHRN => todo!(),
            Op::RSHRN2 => todo!(),
            Op::RSHRNB => todo!(),
            Op::RSHRNT => todo!(),
            Op::RSUBHN => todo!(),
            Op::RSUBHN2 => todo!(),
            Op::RSUBHNB => todo!(),
            Op::RSUBHNT => todo!(),
            Op::SABA => todo!(),
            Op::SABAL => todo!(),
            Op::SABAL2 => todo!(),
            Op::SABALB => todo!(),
            Op::SABALT => todo!(),
            Op::SABD => todo!(),
            Op::SABDL => todo!(),
            Op::SABDL2 => todo!(),
            Op::SABDLB => todo!(),
            Op::SABDLT => todo!(),
            Op::SADALP => todo!(),
            Op::SADDL => todo!(),
            Op::SADDL2 => todo!(),
            Op::SADDLB => todo!(),
            Op::SADDLBT => todo!(),
            Op::SADDLP => todo!(),
            Op::SADDLT => todo!(),
            Op::SADDLV => todo!(),
            Op::SADDV => todo!(),
            Op::SADDW => todo!(),
            Op::SADDW2 => todo!(),
            Op::SADDWB => todo!(),
            Op::SADDWT => todo!(),
            Op::SB => todo!(),
            Op::SBC => todo!(),
            Op::SBCLB => todo!(),
            Op::SBCLT => todo!(),
            Op::SBCS => todo!(),
            Op::SBFIZ => todo!(),
            Op::SBFM => todo!(),
            Op::SBFX => todo!(),
            Op::SCLAMP => todo!(),
            Op::SCVTF => todo!(),
            Op::SDIVR => todo!(),
            Op::SDOT => todo!(),
            Op::SEL => todo!(),
            Op::SETF16 => todo!(),
            Op::SETF8 => todo!(),
            Op::SETFFR => todo!(),
            Op::SEV => todo!(),
            Op::SEVL => todo!(),
            Op::SHA1C => todo!(),
            Op::SHA1H => todo!(),
            Op::SHA1M => todo!(),
            Op::SHA1P => todo!(),
            Op::SHA1SU0 => todo!(),
            Op::SHA1SU1 => todo!(),
            Op::SHA256H => todo!(),
            Op::SHA256H2 => todo!(),
            Op::SHA256SU0 => todo!(),
            Op::SHA256SU1 => todo!(),
            Op::SHA512H => todo!(),
            Op::SHA512H2 => todo!(),
            Op::SHA512SU0 => todo!(),
            Op::SHA512SU1 => todo!(),
            Op::SHADD => todo!(),
            Op::SHL => todo!(),
            Op::SHLL => todo!(),
            Op::SHLL2 => todo!(),
            Op::SHRN => todo!(),
            Op::SHRN2 => todo!(),
            Op::SHRNB => todo!(),
            Op::SHRNT => todo!(),
            Op::SHSUB => todo!(),
            Op::SHSUBR => todo!(),
            Op::SLI => todo!(),
            Op::SM3PARTW1 => todo!(),
            Op::SM3PARTW2 => todo!(),
            Op::SM3SS1 => todo!(),
            Op::SM3TT1A => todo!(),
            Op::SM3TT1B => todo!(),
            Op::SM3TT2A => todo!(),
            Op::SM3TT2B => todo!(),
            Op::SM4E => todo!(),
            Op::SM4EKEY => todo!(),
            Op::SMADDL => todo!(),
            Op::SMAX => todo!(),
            Op::SMAXP => todo!(),
            Op::SMAXV => todo!(),
            Op::SMC => todo!(),
            Op::SMIN => todo!(),
            Op::SMINP => todo!(),
            Op::SMINV => todo!(),
            Op::SMLAL => todo!(),
            Op::SMLAL2 => todo!(),
            Op::SMLALB => todo!(),
            Op::SMLALT => todo!(),
            Op::SMLSL => todo!(),
            Op::SMLSL2 => todo!(),
            Op::SMLSLB => todo!(),
            Op::SMLSLT => todo!(),
            Op::SMMLA => todo!(),
            Op::SMNEGL => todo!(),
            Op::SMOPA => todo!(),
            Op::SMOPS => todo!(),
            Op::SMOV => todo!(),
            Op::SMSTART => todo!(),
            Op::SMSTOP => todo!(),
            Op::SMSUBL => todo!(),
            Op::SMULH => todo!(),
            Op::SMULL => todo!(),
            Op::SMULL2 => todo!(),
            Op::SMULLB => todo!(),
            Op::SMULLT => todo!(),
            Op::SPLICE => todo!(),
            Op::SQABS => todo!(),
            Op::SQADD => todo!(),
            Op::SQCADD => todo!(),
            Op::SQDECB => todo!(),
            Op::SQDECD => todo!(),
            Op::SQDECH => todo!(),
            Op::SQDECP => todo!(),
            Op::SQDECW => todo!(),
            Op::SQDMLAL => todo!(),
            Op::SQDMLAL2 => todo!(),
            Op::SQDMLALB => todo!(),
            Op::SQDMLALBT => todo!(),
            Op::SQDMLALT => todo!(),
            Op::SQDMLSL => todo!(),
            Op::SQDMLSL2 => todo!(),
            Op::SQDMLSLB => todo!(),
            Op::SQDMLSLBT => todo!(),
            Op::SQDMLSLT => todo!(),
            Op::SQDMULH => todo!(),
            Op::SQDMULL => todo!(),
            Op::SQDMULL2 => todo!(),
            Op::SQDMULLB => todo!(),
            Op::SQDMULLT => todo!(),
            Op::SQINCB => todo!(),
            Op::SQINCD => todo!(),
            Op::SQINCH => todo!(),
            Op::SQINCP => todo!(),
            Op::SQINCW => todo!(),
            Op::SQNEG => todo!(),
            Op::SQRDCMLAH => todo!(),
            Op::SQRDMLAH => todo!(),
            Op::SQRDMLSH => todo!(),
            Op::SQRDMULH => todo!(),
            Op::SQRSHL => todo!(),
            Op::SQRSHLR => todo!(),
            Op::SQRSHRN => todo!(),
            Op::SQRSHRN2 => todo!(),
            Op::SQRSHRNB => todo!(),
            Op::SQRSHRNT => todo!(),
            Op::SQRSHRUN => todo!(),
            Op::SQRSHRUN2 => todo!(),
            Op::SQRSHRUNB => todo!(),
            Op::SQRSHRUNT => todo!(),
            Op::SQSHL => todo!(),
            Op::SQSHLR => todo!(),
            Op::SQSHLU => todo!(),
            Op::SQSHRN => todo!(),
            Op::SQSHRN2 => todo!(),
            Op::SQSHRNB => todo!(),
            Op::SQSHRNT => todo!(),
            Op::SQSHRUN => todo!(),
            Op::SQSHRUN2 => todo!(),
            Op::SQSHRUNB => todo!(),
            Op::SQSHRUNT => todo!(),
            Op::SQSUB => todo!(),
            Op::SQSUBR => todo!(),
            Op::SQXTN => todo!(),
            Op::SQXTN2 => todo!(),
            Op::SQXTNB => todo!(),
            Op::SQXTNT => todo!(),
            Op::SQXTUN => todo!(),
            Op::SQXTUN2 => todo!(),
            Op::SQXTUNB => todo!(),
            Op::SQXTUNT => todo!(),
            Op::SRHADD => todo!(),
            Op::SRI => todo!(),
            Op::SRSHL => todo!(),
            Op::SRSHLR => todo!(),
            Op::SRSHR => todo!(),
            Op::SRSRA => todo!(),
            Op::SSBB => todo!(),
            Op::SSHL => todo!(),
            Op::SSHLL => todo!(),
            Op::SSHLL2 => todo!(),
            Op::SSHLLB => todo!(),
            Op::SSHLLT => todo!(),
            Op::SSHR => todo!(),
            Op::SSRA => todo!(),
            Op::SSUBL => todo!(),
            Op::SSUBL2 => todo!(),
            Op::SSUBLB => todo!(),
            Op::SSUBLBT => todo!(),
            Op::SSUBLT => todo!(),
            Op::SSUBLTB => todo!(),
            Op::SSUBW => todo!(),
            Op::SSUBW2 => todo!(),
            Op::SSUBWB => todo!(),
            Op::SSUBWT => todo!(),
            Op::ST1 => todo!(),
            Op::ST1B => todo!(),
            Op::ST1D => todo!(),
            Op::ST1H => todo!(),
            Op::ST1Q => todo!(),
            Op::ST1W => todo!(),
            Op::ST2 => todo!(),
            Op::ST2B => todo!(),
            Op::ST2D => todo!(),
            Op::ST2G => todo!(),
            Op::ST2H => todo!(),
            Op::ST2W => todo!(),
            Op::ST3 => todo!(),
            Op::ST3B => todo!(),
            Op::ST3D => todo!(),
            Op::ST3H => todo!(),
            Op::ST3W => todo!(),
            Op::ST4 => todo!(),
            Op::ST4B => todo!(),
            Op::ST4D => todo!(),
            Op::ST4H => todo!(),
            Op::ST4W => todo!(),
            Op::ST64B => todo!(),
            Op::ST64BV => todo!(),
            Op::ST64BV0 => todo!(),
            Op::STADD => todo!(),
            Op::STADDB => todo!(),
            Op::STADDH => todo!(),
            Op::STADDL => todo!(),
            Op::STADDLB => todo!(),
            Op::STADDLH => todo!(),
            Op::STCLR => todo!(),
            Op::STCLRB => todo!(),
            Op::STCLRH => todo!(),
            Op::STCLRL => todo!(),
            Op::STCLRLB => todo!(),
            Op::STCLRLH => todo!(),
            Op::STEOR => todo!(),
            Op::STEORB => todo!(),
            Op::STEORH => todo!(),
            Op::STEORL => todo!(),
            Op::STEORLB => todo!(),
            Op::STEORLH => todo!(),
            Op::STG => todo!(),
            Op::STGM => todo!(),
            Op::STGP => todo!(),
            Op::STLLR => todo!(),
            Op::STLLRB => todo!(),
            Op::STLLRH => todo!(),
            Op::STLR => todo!(),
            Op::STLRB => todo!(),
            Op::STLRH => todo!(),
            Op::STLUR => todo!(),
            Op::STLURB => todo!(),
            Op::STLURH => todo!(),
            Op::STLXP => todo!(),
            Op::STLXR => todo!(),
            Op::STLXRB => todo!(),
            Op::STLXRH => todo!(),
            Op::STNP => todo!(),
            Op::STNT1B => todo!(),
            Op::STNT1D => todo!(),
            Op::STNT1H => todo!(),
            Op::STNT1W => todo!(),
            Op::STP => todo!(),
            Op::STRB => todo!(),
            Op::STRH => todo!(),
            Op::STSET => todo!(),
            Op::STSETB => todo!(),
            Op::STSETH => todo!(),
            Op::STSETL => todo!(),
            Op::STSETLB => todo!(),
            Op::STSETLH => todo!(),
            Op::STSMAX => todo!(),
            Op::STSMAXB => todo!(),
            Op::STSMAXH => todo!(),
            Op::STSMAXL => todo!(),
            Op::STSMAXLB => todo!(),
            Op::STSMAXLH => todo!(),
            Op::STSMIN => todo!(),
            Op::STSMINB => todo!(),
            Op::STSMINH => todo!(),
            Op::STSMINL => todo!(),
            Op::STSMINLB => todo!(),
            Op::STSMINLH => todo!(),
            Op::STTR => todo!(),
            Op::STTRB => todo!(),
            Op::STTRH => todo!(),
            Op::STUMAX => todo!(),
            Op::STUMAXB => todo!(),
            Op::STUMAXH => todo!(),
            Op::STUMAXL => todo!(),
            Op::STUMAXLB => todo!(),
            Op::STUMAXLH => todo!(),
            Op::STUMIN => todo!(),
            Op::STUMINB => todo!(),
            Op::STUMINH => todo!(),
            Op::STUMINL => todo!(),
            Op::STUMINLB => todo!(),
            Op::STUMINLH => todo!(),
            Op::STUR => todo!(),
            Op::STURB => todo!(),
            Op::STURH => todo!(),
            Op::STXP => todo!(),
            Op::STXR => todo!(),
            Op::STXRB => todo!(),
            Op::STXRH => todo!(),
            Op::STZ2G => todo!(),
            Op::STZG => todo!(),
            Op::STZGM => todo!(),
            Op::SUBG => todo!(),
            Op::SUBHN => todo!(),
            Op::SUBHN2 => todo!(),
            Op::SUBHNB => todo!(),
            Op::SUBHNT => todo!(),
            Op::SUBP => todo!(),
            Op::SUBPS => todo!(),
            Op::SUBR => todo!(),
            Op::SUDOT => todo!(),
            Op::SUMOPA => todo!(),
            Op::SUMOPS => todo!(),
            Op::SUNPKHI => todo!(),
            Op::SUNPKLO => todo!(),
            Op::SUQADD => todo!(),
            Op::SVC => todo!(),
            Op::SWP => todo!(),
            Op::SWPA => todo!(),
            Op::SWPAB => todo!(),
            Op::SWPAH => todo!(),
            Op::SWPAL => todo!(),
            Op::SWPALB => todo!(),
            Op::SWPALH => todo!(),
            Op::SWPB => todo!(),
            Op::SWPH => todo!(),
            Op::SWPL => todo!(),
            Op::SWPLB => todo!(),
            Op::SWPLH => todo!(),
            Op::SXTB => todo!(),
            Op::SXTH => todo!(),
            Op::SXTL => todo!(),
            Op::SXTL2 => todo!(),
            Op::SXTW => todo!(),
            Op::SYS => todo!(),
            Op::SYSL => todo!(),
            Op::TBL => todo!(),
            Op::TBNZ => todo!(),
            Op::TBX => todo!(),
            Op::TBZ => todo!(),
            Op::TCANCEL => todo!(),
            Op::TCOMMIT => todo!(),
            Op::TLBI => {
                // TLB invalidate operation
            }
            Op::TRN1 => todo!(),
            Op::TRN2 => todo!(),
            Op::TSB => todo!(),
            Op::TST => todo!(),
            Op::TSTART => todo!(),
            Op::TTEST => todo!(),
            Op::UABA => todo!(),
            Op::UABAL => todo!(),
            Op::UABAL2 => todo!(),
            Op::UABALB => todo!(),
            Op::UABALT => todo!(),
            Op::UABD => todo!(),
            Op::UABDL => todo!(),
            Op::UABDL2 => todo!(),
            Op::UABDLB => todo!(),
            Op::UABDLT => todo!(),
            Op::UADALP => todo!(),
            Op::UADDL => todo!(),
            Op::UADDL2 => todo!(),
            Op::UADDLB => todo!(),
            Op::UADDLP => todo!(),
            Op::UADDLT => todo!(),
            Op::UADDLV => todo!(),
            Op::UADDV => todo!(),
            Op::UADDW => todo!(),
            Op::UADDW2 => todo!(),
            Op::UADDWB => todo!(),
            Op::UADDWT => todo!(),
            Op::UBFIZ => todo!(),
            Op::UBFM => todo!(),
            Op::UBFX => todo!(),
            Op::UCLAMP => todo!(),
            Op::UCVTF => todo!(),
            Op::UDF => {
                // FIXME: What should we do here?
                return ControlFlow::Break(None);
            }
            Op::UDIV => todo!(),
            Op::UDIVR => todo!(),
            Op::UDOT => todo!(),
            Op::UHADD => todo!(),
            Op::UHSUB => todo!(),
            Op::UHSUBR => todo!(),
            Op::UMADDL => todo!(),
            Op::UMAX => todo!(),
            Op::UMAXP => todo!(),
            Op::UMAXV => todo!(),
            Op::UMIN => todo!(),
            Op::UMINP => todo!(),
            Op::UMINV => todo!(),
            Op::UMLAL => todo!(),
            Op::UMLAL2 => todo!(),
            Op::UMLALB => todo!(),
            Op::UMLALT => todo!(),
            Op::UMLSL => todo!(),
            Op::UMLSL2 => todo!(),
            Op::UMLSLB => todo!(),
            Op::UMLSLT => todo!(),
            Op::UMMLA => todo!(),
            Op::UMNEGL => todo!(),
            Op::UMOPA => todo!(),
            Op::UMOPS => todo!(),
            Op::UMOV => todo!(),
            Op::UMSUBL => todo!(),
            Op::UMULH => todo!(),
            Op::UMULL => todo!(),
            Op::UMULL2 => todo!(),
            Op::UMULLB => todo!(),
            Op::UMULLT => todo!(),
            Op::UQADD => todo!(),
            Op::UQDECB => todo!(),
            Op::UQDECD => todo!(),
            Op::UQDECH => todo!(),
            Op::UQDECP => todo!(),
            Op::UQDECW => todo!(),
            Op::UQINCB => todo!(),
            Op::UQINCD => todo!(),
            Op::UQINCH => todo!(),
            Op::UQINCP => todo!(),
            Op::UQINCW => todo!(),
            Op::UQRSHL => todo!(),
            Op::UQRSHLR => todo!(),
            Op::UQRSHRN => todo!(),
            Op::UQRSHRN2 => todo!(),
            Op::UQRSHRNB => todo!(),
            Op::UQRSHRNT => todo!(),
            Op::UQSHL => todo!(),
            Op::UQSHLR => todo!(),
            Op::UQSHRN => todo!(),
            Op::UQSHRN2 => todo!(),
            Op::UQSHRNB => todo!(),
            Op::UQSHRNT => todo!(),
            Op::UQSUB => todo!(),
            Op::UQSUBR => todo!(),
            Op::UQXTN => todo!(),
            Op::UQXTN2 => todo!(),
            Op::UQXTNB => todo!(),
            Op::UQXTNT => todo!(),
            Op::URECPE => todo!(),
            Op::URHADD => todo!(),
            Op::URSHL => todo!(),
            Op::URSHLR => todo!(),
            Op::URSHR => todo!(),
            Op::URSQRTE => todo!(),
            Op::URSRA => todo!(),
            Op::USDOT => todo!(),
            Op::USHL => todo!(),
            Op::USHLL => todo!(),
            Op::USHLL2 => todo!(),
            Op::USHLLB => todo!(),
            Op::USHLLT => todo!(),
            Op::USHR => todo!(),
            Op::USMMLA => todo!(),
            Op::USMOPA => todo!(),
            Op::USMOPS => todo!(),
            Op::USQADD => todo!(),
            Op::USRA => todo!(),
            Op::USUBL => todo!(),
            Op::USUBL2 => todo!(),
            Op::USUBLB => todo!(),
            Op::USUBLT => todo!(),
            Op::USUBW => todo!(),
            Op::USUBW2 => todo!(),
            Op::USUBWB => todo!(),
            Op::USUBWT => todo!(),
            Op::UUNPKHI => todo!(),
            Op::UUNPKLO => todo!(),
            Op::UXTB => todo!(),
            Op::UXTH => todo!(),
            Op::UXTL => todo!(),
            Op::UXTL2 => todo!(),
            Op::UXTW => todo!(),
            Op::UZP1 => todo!(),
            Op::UZP2 => todo!(),
            Op::WFE => todo!(),
            Op::WFET => todo!(),
            Op::WFI => todo!(),
            Op::WFIT => todo!(),
            Op::WHILEGE => todo!(),
            Op::WHILEGT => todo!(),
            Op::WHILEHI => todo!(),
            Op::WHILEHS => todo!(),
            Op::WHILELE => todo!(),
            Op::WHILELO => todo!(),
            Op::WHILELS => todo!(),
            Op::WHILELT => todo!(),
            Op::WHILERW => todo!(),
            Op::WHILEWR => todo!(),
            Op::WRFFR => todo!(),
            Op::XAFLAG => todo!(),
            Op::XAR => todo!(),
            Op::XPACD => todo!(),
            Op::XPACI => todo!(),
            Op::XPACLRI => todo!(),
            Op::XTN => todo!(),
            Op::XTN2 => todo!(),
            Op::YIELD => todo!(),
            Op::ZERO => todo!(),
            Op::ZIP1 => todo!(),
            Op::ZIP2 => todo!(),
        }
        ControlFlow::Continue(())
    }

    fn emit_jump(&mut self, pc_value: Value) {
        {
            {
                let Self {
                    ref mut cpu_state,
                    ref mut builder,
                    ref registers,
                    ref sys_registers,
                    ..
                } = self;
                cpu_state.save_cpu_state(builder, registers, sys_registers);
            }
            self.builder.ins().store(
                MemFlags::trusted().with_vmctx(),
                pc_value,
                self.machine_ptr,
                std::mem::offset_of!(Armv8AMachine, pc) as i32,
            );
            let translate_func = self.builder.ins().load(
                self.pointer_type,
                MemFlags::trusted().with_vmctx(),
                self.machine_ptr,
                std::mem::offset_of!(Armv8AMachine, lookup_entry_func) as i32,
            );
            let call = self.builder.ins().call_indirect(
                self.sigref,
                translate_func,
                &[self.jit_ctx_ptr, self.machine_ptr],
            );
            let resolved_entry = self.builder.inst_results(call)[0];
            self.builder.ins().return_(&[resolved_entry]);
        }
    }

    fn emit_halt(&mut self) {
        {
            let Self {
                ref mut cpu_state,
                ref mut builder,
                ref registers,
                ref sys_registers,
                ..
            } = self;
            cpu_state.save_cpu_state(builder, registers, sys_registers);
        }
        let bool_type = cranelift::prelude::Type::int(8).expect("Could not create bool type");
        let true_value = self.builder.ins().iconst(bool_type, 1);
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            true_value,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, halted) as i32,
        );
        let translate_func = self.builder.ins().load(
            self.pointer_type,
            MemFlags::trusted().with_vmctx(),
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, lookup_entry_func) as i32,
        );
        let call = self.builder.ins().call_indirect(
            self.sigref,
            translate_func,
            &[self.jit_ctx_ptr, self.machine_ptr],
        );
        let resolved_entry = self.builder.inst_results(call)[0];
        self.builder.ins().return_(&[resolved_entry]);
    }
}
