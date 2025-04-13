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

//! Generation of JIT code as translation blocks.

use std::{ops::ControlFlow, pin::Pin};

use codegen::ir::types::{I64, I8};
use cranelift::{codegen::ir::immediates::Offset32, prelude::*};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use indexmap::IndexMap;
use num_traits::cast::FromPrimitive;

use crate::{cpu_state::ExecutionState, machine::Armv8AMachine};

#[repr(transparent)]
#[derive(Clone, Copy)]
/// An "entry" function for a block.
///
/// It can be either a JIT compiled translation block, or a special emulator
/// function.
pub struct Entry(pub extern "C" fn(&mut JitContext, &mut Armv8AMachine) -> Entry);

/// Lookup [`machine.pc`] in cached entry blocks
/// ([`Armv8AMachine::entry_blocks`]).
#[no_mangle]
pub extern "C" fn lookup_entry(context: &mut JitContext, machine: &mut Armv8AMachine) -> Entry {
    let pc: u64 = machine.pc;
    if let Some(entry) = machine.entry_blocks.get(&pc) {
        log::trace!("lookup entry entry found for 0x{:x}", pc);
        return *entry;
    }
    log::trace!("generating entry for pc 0x{:x}", pc);

    let next_entry = context.compile(machine, pc.try_into().unwrap()).unwrap();
    machine.entry_blocks.insert(pc, next_entry);

    log::trace!("returning generated entry for pc 0x{:x}", pc);
    next_entry
}

#[inline]
fn is_vector(reg: &bad64::Reg) -> bool {
    use bad64::Reg;
    let reg = *reg as u32;
    ((Reg::V0 as u32)..=(Reg::Q31 as u32)).contains(&reg)
}

/// JIT context/builder used to disassemble code and JIT compile it.
pub struct JitContext {
    /// The function builder context, which is reused across multiple
    /// `FunctionBuilder` instances.
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
    /// Returns a new [`JitContext`].
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

    /// Performs compilation of a block starting at `program_counter`] and
    /// returns an [`Entry`] for it.
    pub fn compile(
        &mut self,
        machine: &mut Armv8AMachine,
        program_counter: usize,
    ) -> Result<Entry, Box<dyn std::error::Error>> {
        log::trace!("jit compile called for pc = 0x{:x}", program_counter);
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

        // We generate the translated block as a Cranelift function.
        //
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

    /// Translate instructions starting from address `program_counter`.
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
        let mut trans = BlockTranslator {
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
                    log::trace!("0x{:x}: {}", insn.address(), insn);
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
        let BlockTranslator { builder, .. } = trans;

        // Tell the builder we're done with this block (function in Cranelift terms).
        builder.finalize();
        Ok(())
    }
}

/// In-progress state of translating instructions into Cranelift IR.
struct BlockTranslator<'a> {
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

#[derive(Clone, Copy)]
#[repr(i32)]
/// Register/memory width in bits.
enum Width {
    _128 = 128,
    _64 = 64,
    _32 = 32,
    _16 = 16,
    _8 = 8,
}

impl BlockTranslator<'_> {
    #[allow(non_snake_case)]
    /// Return [`Value`] for special registers.
    fn translate_o0_op1_CRn_CRm_op2(&mut self, o0: u8, o1: u8, cm: u8, cn: u8, o2: u8) -> Value {
        match (o0, o1, cm, cn, o2) {
            (0b11, 0, 0, 0b111, 0) => {
                // [ref:FIXME]: ID_AA64MMFR0_EL1
                self.builder.ins().iconst(I64, 0)
            }
            (0b11, 0, 0, 0, 0) => {
                // [ref:FIXME]: MIDR_EL1
                self.builder.ins().iconst(I64, 0)
            }
            (3, 0, 0, 0, 5) => {
                // [ref:FIXME]: MPIDR_EL1
                self.builder.ins().iconst(I64, 0)
            }
            _other => unimplemented!(
                "unimplemented sysreg encoding: {:?}",
                bad64::Operand::ImplSpec { o0, o1, cm, cn, o2 }
            ),
        }
    }

    /// Perform `AddWithCarry` operation.
    ///
    /// Integer addition with carry input, returning result and NZCV flags
    fn add_with_carry(&mut self, x: Value, y: Value, carry_in: bool) -> (Value, [Value; 4]) {
        let (mut unsigned_sum, mut overflow_1) = self.builder.ins().uadd_overflow(x, y);
        if carry_in {
            let one = self.builder.ins().iconst(I64, 1);
            let (carry_add, carry_overflow) = self.builder.ins().uadd_overflow(unsigned_sum, one);
            unsigned_sum = carry_add;
            overflow_1 = self.builder.ins().bor(overflow_1, carry_overflow);
        }
        let (mut signed_sum, mut overflow_2) = self.builder.ins().sadd_overflow(x, y);
        if carry_in {
            let one = self.builder.ins().iconst(I64, 1);
            let (carry_add, carry_overflow) = self.builder.ins().sadd_overflow(signed_sum, one);
            signed_sum = carry_add;
            overflow_2 = self.builder.ins().bor(overflow_2, carry_overflow);
        }
        let nth_bit_mask = self
            .builder
            .ins()
            .iconst(I64, (u64::MAX & !(1 << 63)) as i64);
        eprintln!("u64::MAX & !(1 << 64) = 0x:{:x}", u64::MAX & !(1 << 63));
        let result = self.builder.ins().band(unsigned_sum, nth_bit_mask);
        let n = self
            .builder
            .ins()
            .icmp_imm(IntCC::SignedLessThan, signed_sum, 0);
        let z = self.builder.ins().icmp_imm(IntCC::Equal, result, 0);
        let c = self.builder.ins().icmp_imm(IntCC::NotEqual, overflow_2, 0);
        let v = self.builder.ins().icmp_imm(IntCC::NotEqual, overflow_1, 0);
        let n = self.builder.ins().uextend(I64, n);
        let z = self.builder.ins().uextend(I64, z);
        let c = self.builder.ins().uextend(I64, c);
        let v = self.builder.ins().uextend(I64, v);
        // [ref:verify_implementation]: make sure what kind of int bit width nzcv have
        // let n = self.builder.ins().ireduce(I8, n);
        // let z = self.builder.ins().ireduce(I8, z);
        // let c = self.builder.ins().ireduce(I8, c);
        // let v = self.builder.ins().ireduce(I8, v);
        // (bits(N), bits(4)) AddWithCarry(bits(N) x, bits(N) y, bit carry_in)
        // constant integer unsigned_sum = UInt(x) + UInt(y) + UInt(carry_in);
        // constant integer signed_sum = SInt(x) + SInt(y) + UInt(carry_in);
        // constant bits(N) result = unsigned_sum<N-1:0>; // same value as
        // signed_sum<N-1:0> constant bit n = result<N-1>;
        // constant bit z = if IsZero(result) then '1' else '0';
        // constant bit c = if UInt(result) == unsigned_sum then '0' else '1';
        // constant bit v = if SInt(result) == signed_sum then '0' else '1';
        // return (result, n:z:c:v);
        (result, [n, z, c, v])
    }

    /// Update CPU state of NZCV flags.
    fn update_nzcv(&mut self, [n, z, c, v]: [Value; 4]) {
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            n,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, cpu_state.pstate.N) as i32,
        );
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            z,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, cpu_state.pstate.Z) as i32,
        );
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            c,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, cpu_state.pstate.C) as i32,
        );
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            v,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, cpu_state.pstate.V) as i32,
        );
    }

    fn branch_if_non_zero(&mut self, is_zero_value: Value, label_value: Value) {
        let branch_not_taken_block = self.builder.create_block();
        let branch_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, I64);
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
        self.emit_jump(label_value);
        // Switch to the merge block for subsequent statements.
        self.builder.switch_to_block(merge_block);

        // We've now seen all the predecessors of the merge block.
        self.builder.seal_block(merge_block);
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
                        let imm_value =
                            self.builder.ins().iconst(I64, i64::try_from(*imm).unwrap());
                        let value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        let reg_var = *self.reg_to_var(reg, true);
                        self.builder.def_var(reg_var, value);
                        self.reg_to_value(reg)
                    }
                    Imm::Signed(imm) if *imm < 0 => {
                        let imm_value = self.builder.ins().iconst(I64, (*imm).abs());
                        let (value, _overflow_flag) =
                            self.builder.ins().usub_overflow(reg_val, imm_value);
                        let reg_var = *self.reg_to_var(reg, true);
                        self.builder.def_var(reg_var, value);
                        self.reg_to_value(reg)
                    }
                    Imm::Signed(imm) => {
                        let imm_value = self.builder.ins().iconst(I64, *imm);
                        let value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        let reg_var = *self.reg_to_var(reg, true);
                        self.builder.def_var(reg_var, value);
                        self.reg_to_value(reg)
                    }
                }
            }
            Operand::MemPostIdxImm { ref reg, imm } => {
                let reg_val = self.reg_to_value(reg);
                match imm {
                    Imm::Unsigned(imm) => {
                        let imm_value =
                            self.builder.ins().iconst(I64, i64::try_from(*imm).unwrap());
                        let post_value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, post_value);
                    }
                    Imm::Signed(imm) if *imm < 0 => {
                        let imm_value = self.builder.ins().iconst(I64, (*imm).abs());
                        let (post_value, _overflow_flag) =
                            self.builder.ins().usub_overflow(reg_val, imm_value);
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, post_value);
                    }
                    Imm::Signed(imm) => {
                        let imm_value = self.builder.ins().iconst(I64, *imm);
                        let post_value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        let reg_var = *self.reg_to_var(reg, false);
                        self.builder.def_var(reg_var, post_value);
                    }
                }
                reg_val
            }
            Operand::Imm64 { imm, shift } => {
                let const_value = match imm {
                    Imm::Unsigned(imm) => {
                        self.builder.ins().iconst(I64, i64::try_from(*imm).unwrap())
                    }
                    Imm::Signed(imm) => self.builder.ins().iconst(I64, *imm),
                };
                match shift {
                    None => const_value,
                    Some(bad64::Shift::LSL(lsl)) => {
                        let lsl = self.builder.ins().iconst(I64, i64::from(*lsl));
                        self.builder.ins().ishl(const_value, lsl)
                    }
                    other => unimplemented!("unimplemented shift {other:?}"),
                }
            }
            Operand::Imm32 { imm, shift } => {
                let const_value = match imm {
                    Imm::Unsigned(imm) => self.builder.ins().iconst(I64, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iconst(I64, *imm),
                };
                match shift {
                    None => const_value,
                    Some(bad64::Shift::LSL(lsl)) => {
                        let lsl = self.builder.ins().iconst(I64, i64::from(*lsl));
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
                        let imm_value =
                            self.builder.ins().iconst(I64, i64::try_from(*imm).unwrap());
                        let value = self.builder.ins().uadd_overflow_trap(
                            reg_val,
                            imm_value,
                            TrapCode::IntegerOverflow,
                        );
                        value
                    }
                    Imm::Signed(imm) if *imm < 0 => {
                        let imm_value = self.builder.ins().iconst(I64, (*imm).abs());
                        let (value, _overflow_flag) =
                            self.builder.ins().usub_overflow(reg_val, imm_value);
                        value
                    }
                    Imm::Signed(imm) => {
                        let imm_value = self.builder.ins().iconst(I64, *imm);
                        let (value, _overflow_flag) =
                            self.builder.ins().uadd_overflow(reg_val, imm_value);
                        value
                    }
                }
            }
            Operand::Label(Imm::Unsigned(imm)) => self.builder.ins().iconst(I64, *imm as i64),
            Operand::Label(Imm::Signed(imm)) => self.builder.ins().iconst(I64, *imm),
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

    #[cold]
    fn simd_reg_to_var(&mut self, reg: &bad64::Reg, write: bool) -> &Variable {
        use bad64::Reg;

        let reg_no = *reg as u32;
        if ((Reg::V0 as u32)..=(Reg::V31 as u32)).contains(&reg_no) {
            unimplemented!()
            // return &self.registers[reg];
        }
        if ((Reg::Q0 as u32)..=(Reg::Q31 as u32)).contains(&reg_no) {
            unimplemented!()
            // // 128 bits
            // let i = reg_no - (Reg::Q0 as u32);
            // let v_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            // let var = &self.registers[&v_reg];
            // if write {
            //     todo!()
            // }
            // return var;
        }
        if ((Reg::B0 as u32)..=(Reg::B31 as u32)).contains(&reg_no) {
            // 8 bits
            let i = reg_no - (Reg::B0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            if write {
                let mask = self.builder.ins().iconst(I64, 0xff);
                let unmasked_value = self.builder.use_var(self.registers[&d_reg]);
                let masked_value = self.builder.ins().band(unmasked_value, mask);
                self.builder.def_var(self.registers[&d_reg], masked_value);
            }
            return var;
        }
        if ((Reg::H0 as u32)..=(Reg::H31 as u32)).contains(&reg_no) {
            // 16 bits
            let i = reg_no - (Reg::H0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            if write {
                let mask = self.builder.ins().iconst(I64, 0xffff);
                let unmasked_value = self.builder.use_var(self.registers[&d_reg]);
                let masked_value = self.builder.ins().band(unmasked_value, mask);
                self.builder.def_var(self.registers[&d_reg], masked_value);
            }
            return var;
        }
        if ((Reg::S0 as u32)..=(Reg::S31 as u32)).contains(&reg_no) {
            // 32 bits
            let i = reg_no - (Reg::S0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            if write {
                let mask = self.builder.ins().iconst(I64, 0xffff_ffff);
                let unmasked_value = self.builder.use_var(self.registers[&d_reg]);
                let masked_value = self.builder.ins().band(unmasked_value, mask);
                self.builder.def_var(self.registers[&d_reg], masked_value);
            }
            return var;
        }
        if ((Reg::D0 as u32)..=(Reg::D31 as u32)).contains(&reg_no) {
            // 64 bits
            let i = reg_no - (Reg::D0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            return &self.registers[&d_reg];
        }
        unreachable!()
    }

    #[inline]
    fn reg_to_var(&mut self, reg: &bad64::Reg, write: bool) -> &Variable {
        use bad64::Reg;

        if is_vector(reg) {
            return self.simd_reg_to_var(reg, write);
        }

        if reg.is_sve() {
            todo!();
        }

        if reg.is_pred() {
            todo!();
        }

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
            let mask = self.builder.ins().iconst(I64, 0xffff_ffff);
            let unmasked_value = self.builder.use_var(self.registers[&reg_64]);
            let masked_value = self.builder.ins().band(unmasked_value, mask);
            self.builder.def_var(self.registers[&reg_64], masked_value);
        }
        &self.registers[&reg_64]
    }

    #[cold]
    fn simd_reg_to_value(&mut self, reg: &bad64::Reg) -> Value {
        use bad64::Reg;

        let reg_no = *reg as u32;
        if ((Reg::V0 as u32)..=(Reg::V31 as u32)).contains(&reg_no) {
            unimplemented!()
            // return self.builder.use_var(self.registers[reg]);
        }
        if ((Reg::Q0 as u32)..=(Reg::Q31 as u32)).contains(&reg_no) {
            unimplemented!()
            // // 128 bits
            // let i = reg_no - (Reg::Q0 as u32);
            // let v_reg = Reg::from_u32(i + Reg::V0 as u32).unwrap();
            // let var = &self.registers[&v_reg];
            // return self.builder.use_var(*var);
        }
        if ((Reg::B0 as u32)..=(Reg::B31 as u32)).contains(&reg_no) {
            // 8 bits
            let i = reg_no - (Reg::B0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            let value = self.builder.use_var(*var);
            let mask = self.builder.ins().iconst(I64, 0xff);
            return self.builder.ins().band(value, mask);
        }
        if ((Reg::H0 as u32)..=(Reg::H31 as u32)).contains(&reg_no) {
            // 16 bits
            let i = reg_no - (Reg::H0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            let value = self.builder.use_var(*var);
            let mask = self.builder.ins().iconst(I64, 0xffff);
            return self.builder.ins().band(value, mask);
        }
        if ((Reg::S0 as u32)..=(Reg::S31 as u32)).contains(&reg_no) {
            // 32 bits
            let i = reg_no - (Reg::S0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            let value = self.builder.use_var(*var);
            let mask = self.builder.ins().iconst(I64, 0xffff_ffff);
            return self.builder.ins().band(value, mask);
        }
        if ((Reg::D0 as u32)..=(Reg::D31 as u32)).contains(&reg_no) {
            // 64 bits
            let i = reg_no - (Reg::D0 as u32);
            let d_reg = Reg::from_u32(i + Reg::D0 as u32).unwrap();
            let var = &self.registers[&d_reg];
            return self.builder.use_var(*var);
        }
        unreachable!()
    }

    #[inline]
    fn reg_to_value(&mut self, reg: &bad64::Reg) -> Value {
        use bad64::Reg;

        if is_vector(reg) {
            return self.simd_reg_to_value(reg);
        }

        if reg.is_sve() {
            todo!();
        }

        if reg.is_pred() {
            todo!();
        }

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
                return self.builder.ins().iconst(I64, 0);
            }
            _ => {
                let var = &self.registers[reg];
                return self.builder.use_var(*var);
            }
        };
        // Reads from W registers ignore the higher 32 bits of the corresponding X
        // register and leave them unchanged.
        let mask = self.builder.ins().iconst(I64, 0xffff_ffff);
        let unmasked_value = self.builder.use_var(self.registers[&reg_64]);
        let masked_value = self.builder.ins().band(unmasked_value, mask);
        masked_value
    }

    fn operand_width(&mut self, operand: &bad64::Operand) -> Width {
        use bad64::{Operand, Reg};

        let reg = match operand {
            Operand::MemOffset { reg, .. }
            | Operand::MemPreIdx { reg, .. }
            | Operand::MemPostIdxImm { reg, .. }
            | Operand::MemReg(reg)
            | Operand::ShiftReg { reg, .. }
            | Operand::QualReg { reg, .. }
            | Operand::Reg { reg, .. } => reg,
            Operand::ImplSpec { .. } | Operand::SysReg { .. } => return Width::_64,
            Operand::FImm32(_) | Operand::Imm32 { .. } => return Width::_32,
            Operand::Label(_) | Operand::Imm64 { .. } => return Width::_64,
            Operand::MultiReg { .. }
            | Operand::MemPostIdxReg(_)
            | Operand::MemExt { .. }
            | Operand::SmeTile { .. }
            | Operand::AccumArray { .. }
            | Operand::IndexedElement { .. }
            | Operand::Cond(_)
            | Operand::Name(_)
            | Operand::StrImm { .. } => unimplemented!(),
        };

        let reg_val = *reg as u32;
        if ((Reg::W0 as u32)..=(Reg::W30 as u32)).contains(&reg_val)
            || matches!(reg, Reg::WSP | Reg::WZR)
        {
            Width::_32
        } else {
            Width::_64
        }
    }

    /// JIT a single instrunction.
    fn translate_instruction(
        &mut self,
        instruction: bad64::Instruction,
    ) -> ControlFlow<Option<Value>> {
        use bad64::Op;

        if cfg!(feature = "accurate-pc") {
            let pc_value = self
                .builder
                .ins()
                .iconst(I64, i64::try_from(instruction.address()).unwrap());
            self.builder.ins().store(
                MemFlags::trusted().with_vmctx(),
                pc_value,
                self.machine_ptr,
                std::mem::offset_of!(Armv8AMachine, pc) as i32,
            );
        }
        let op = instruction.op();
        match op {
            Op::NOP => {}
            // Special registers
            Op::MSR => {
                // [ref:can_trap]
                let target = match instruction.operands()[0] {
                    bad64::Operand::SysReg(ref sysreg) => *self.sysreg_to_var(sysreg),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let value = self.translate_operand(&instruction.operands()[1]);
                self.builder.def_var(target, value);
            }
            Op::MRS => {
                // Move System register to general-purpose register
                // [ref:can_trap]
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
                let value = self.translate_operand(&instruction.operands()[1]);
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
                let pc = self.builder.ins().iconst(I64, instruction.address() as i64);
                let value =
                    self.builder
                        .ins()
                        .uadd_overflow_trap(pc, imm_value, TrapCode::IntegerOverflow);
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
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let target = self.builder.ins().uadd_overflow_trap(
                    target,
                    mem_start,
                    TrapCode::IntegerOverflow,
                );
                self.builder.ins().store(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    Offset32::new(0),
                );
            }
            Op::STRH => {
                let value = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => self.reg_to_value(reg),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let target = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let target = self.builder.ins().uadd_overflow_trap(
                    target,
                    mem_start,
                    TrapCode::IntegerOverflow,
                );
                self.builder.ins().istore16(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    Offset32::new(0),
                );
            }
            Op::STLRB | Op::STRB => {
                // For STLRB: [ref:atomics]: We don't model exclusive access (yet).
                let value = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => self.reg_to_value(reg),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let target = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let target = self.builder.ins().uadd_overflow_trap(
                    target,
                    mem_start,
                    TrapCode::IntegerOverflow,
                );
                self.builder.ins().istore8(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    Offset32::new(0),
                );
            }
            Op::STP => {
                let width = self.operand_width(&instruction.operands()[0]);
                let data1 = self.translate_operand(&instruction.operands()[0]);
                let data2 = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let target = self.translate_operand(&instruction.operands()[2]);
                let target = self.builder.ins().uadd_overflow_trap(
                    target,
                    mem_start,
                    TrapCode::IntegerOverflow,
                );
                let offset = Offset32::new(width as i32);
                self.builder.ins().store(
                    cranelift::prelude::MemFlags::new(),
                    data1,
                    target,
                    Offset32::new(0),
                );
                self.builder.ins().store(
                    cranelift::prelude::MemFlags::new(),
                    data2,
                    target,
                    offset,
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
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let source_address = self.builder.ins().uadd_overflow_trap(
                    mem_start,
                    source_address,
                    TrapCode::IntegerOverflow,
                );
                let value =
                    self.builder
                        .ins()
                        .load(I64, MemFlags::new(), source_address, Offset32::new(0));
                self.builder.def_var(target, value);
            }
            Op::LDRH => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let source_address = self.builder.ins().uadd_overflow_trap(
                    mem_start,
                    source_address,
                    TrapCode::IntegerOverflow,
                );
                let value = self.builder.ins().uload16(
                    I64,
                    MemFlags::new(),
                    source_address,
                    Offset32::new(0),
                );
                self.builder.def_var(target, value);
            }
            Op::LDRB => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let source_address = self.builder.ins().uadd_overflow_trap(
                    mem_start,
                    source_address,
                    TrapCode::IntegerOverflow,
                );
                let value = self.builder.ins().uload8(
                    I64,
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
                    bad64::Operand::Imm32 { imm, shift } | bad64::Operand::Imm64 { imm, shift } => {
                        let const_value = match imm {
                            bad64::Imm::Unsigned(imm) => {
                                self.builder.ins().iconst(I64, i64::try_from(*imm).unwrap())
                            }
                            bad64::Imm::Signed(imm) => self.builder.ins().iconst(I64, *imm),
                        };
                        match shift {
                            None => (const_value, !0xf),
                            Some(bad64::Shift::LSL(lsl)) => {
                                let lsl_value = self.builder.ins().iconst(I64, i64::from(*lsl));
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
                let mask = self.builder.ins().iconst(I64, shift_mask as i64);
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
                let value = self
                    .builder
                    .ins()
                    .uadd_overflow_trap(a, b, TrapCode::IntegerOverflow);
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
                // [ref:FIXME]: update NZCV flags
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
                // [ref:verify_implementation]

                // constant bits(datasize) operand1 = X[n, datasize];
                // constant bits(datasize) operand2 = X[m, datasize];
                // constant integer dividend = SInt(operand1);
                // constant integer divisor  = SInt(operand2);
                // integer result;
                // if divisor == 0 then
                // result = 0;
                // elsif (dividend < 0) == (divisor < 0) then
                // result = Abs(dividend) DIV Abs(divisor);    // same signs - positive result
                // else
                // result = -(Abs(dividend) DIV Abs(divisor)); // different signs - negative
                // result X[d, datasize] = result<datasize-1:0>;
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

                self.builder.append_block_param(merge_block, I64);

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
            Op::UDIV => {
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

                self.builder.append_block_param(merge_block, I64);

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
                let else_return = self.builder.ins().udiv(dividend, divisor);
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
                let next_pc = self.builder.ins().iconst(I64, label as i64);
                return self.unconditional_jump_epilogue(&instruction, next_pc);
            }
            Op::BR => {
                // This instruction branches unconditionally to an address in a register, with a
                // hint that this is not a subroutine return.
                // constant bits(64) target = X[n, 64];
                // constant boolean branch_conditional = FALSE;
                // BranchTo(target, BranchType_INDIR, branch_conditional);
                let next_pc = self.translate_operand(&instruction.operands()[0]);
                return self.unconditional_jump_epilogue(&instruction, next_pc);
            }
            Op::RET => {
                let next_pc = self.reg_to_value(&bad64::Reg::X30);
                return self.unconditional_jump_epilogue(&instruction, next_pc);
            }
            // Compares
            Op::CBNZ => {
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let label = match instruction.operands()[1] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!("unexpected branch address in {op:?}: {:?}", other),
                };
                let zero = self.reg_to_value(&bad64::Reg::XZR);
                let is_zero_value =
                    self.builder
                        .ins()
                        .icmp(cranelift::prelude::IntCC::Equal, operand1, zero);
                let is_zero_value = self.builder.ins().sextend(I64, is_zero_value);
                let label_value = self.builder.ins().iconst(I64, label as i64);
                self.branch_if_non_zero(is_zero_value, label_value);
            }
            Op::CBZ => {
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let label = match instruction.operands()[1] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!("unexpected branch address in {op:?}: {:?}", other),
                };
                let zero = self.reg_to_value(&bad64::Reg::XZR);
                let is_not_zero_value =
                    self.builder
                        .ins()
                        .icmp(cranelift::prelude::IntCC::NotEqual, operand1, zero);
                let is_not_zero_value = self.builder.ins().sextend(I64, is_not_zero_value);
                let label_value = self.builder.ins().iconst(I64, label as i64);
                self.branch_if_non_zero(is_not_zero_value, label_value);
            }
            // Bit-ops
            Op::BFI => {
                // Bitfield insert
                // [ref:verify_implementation]

                // This instruction copies a bitfield of <width> bits from the least significant
                // bits of the source register to bit position <lsb> of the destination
                // register, leaving the other destination bits unchanged.

                // if sf == '1' && N != '1' then EndOfDecode(Decode_UNDEF);
                //  if sf == '0' && (N != '0' || immr<5> != '0' || imms<5> != '0') then
                // EndOfDecode(Decode_UNDEF);

                //  constant integer d = UInt(Rd);
                //  constant integer n = UInt(Rn);
                //  constant integer datasize = 32 << UInt(sf);
                //  constant integer s = UInt(imms);
                //  constant integer r = UInt(immr);

                //  bits(datasize) wmask;
                //  bits(datasize) tmask;
                //  (wmask, tmask) = DecodeBitMasks(N, imms, immr, FALSE, datasize);
                // constant bits(datasize) dst = X[d, datasize];
                // constant bits(datasize) src = X[n, datasize];

                // // Perform bitfield move on low bits
                // constant bits(datasize) bot = (dst AND NOT(wmask)) OR (ROR(src, r) AND
                // wmask);

                // // Combine extension bits and result bits
                // X[d, datasize] = (dst AND NOT(tmask)) OR (bot AND tmask);
                let dst = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let dst_value = self.translate_operand(&instruction.operands()[0]);
                let src_value = self.translate_operand(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let wmask = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(wmask),
                        shift: None,
                    } => self.builder.ins().iconst(I64, 2_i64.pow(wmask as u32) - 1),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let bits_to_copy = self.builder.ins().band(wmask, src_value);
                let bits_mask = self.builder.ins().rotl_imm(bits_to_copy, lsb);
                let target_mask = self.builder.ins().rotl_imm(wmask, lsb);
                let target_mask = self.builder.ins().bnot(target_mask);
                let dst_value = self.builder.ins().band(target_mask, dst_value);
                let dst_value = self.builder.ins().bor(dst_value, bits_mask);
                self.builder.def_var(dst, dst_value);
            }
            Op::ORR => {
                // Bitwise OR
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
            Op::AND => {
                // Bitwise AND
                // This instruction performs a bitwise AND of a register value and an immediate
                // value, and writes the result to the destination register.
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().band(a, b);
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
            Op::LSR => {
                // Logical shift right
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().ushr(a, b);
                self.builder.def_var(target, value);
            }
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
            Op::BL => {
                let link_pc = instruction.address() + 4;
                let link_pc = self.builder.ins().iconst(I64, link_pc as i64);
                let link_register = *self.reg_to_var(&bad64::Reg::X30, true);
                self.builder.def_var(link_register, link_pc);
                let label = match instruction.operands()[0] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!("unexpected branch address in {op:?}: {:?}", other),
                };
                let label_value = self.builder.ins().iconst(I64, label as i64);
                return self.unconditional_jump_epilogue(&instruction, label_value);
            }
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
            Op::B_CS => {
                let carry_is_set = self.builder.ins().load(
                    I64,
                    MemFlags::trusted().with_vmctx(),
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, cpu_state.pstate.C) as i32,
                );
                let label = match instruction.operands()[0] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!("unexpected branch address in {op:?}: {:?}", other),
                };
                // let carry_is_set = self.builder.ins().uextend(I64, carry_is_set);
                let label_value = self.builder.ins().iconst(I64, label as i64);
                self.branch_if_non_zero(carry_is_set, label_value);
            }
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
            Op::CCMN => todo!(),
            Op::CCMP => todo!(),
            Op::CDOT => todo!(),
            Op::CFINV => todo!(),
            Op::CFP => todo!(),
            Op::CINC => todo!(),
            Op::CINV => todo!(),
            Op::CLASTA => todo!(),
            Op::CLASTB => todo!(),
            Op::CLREX => {
                // [ref:atomics]: We don't model exclusive access (yet).
            }
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
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let operand2 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.builder.ins().bnot(operand2);
                let (_result, nzcv) = self.add_with_carry(operand1, operand2, true);
                // discard result, only update NZCV flags.
                self.update_nzcv(nzcv);
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
            Op::CSEL => todo!(),
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
                // [ref:FIXME]: select current EL from PSTATE, and jump to ELR_ELx.
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
            Op::LDAXRB => {
                // [ref:atomics]: We don't model exclusive access (yet).
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let source_address = self.builder.ins().uadd_overflow_trap(
                    mem_start,
                    source_address,
                    TrapCode::IntegerOverflow,
                );
                let value = self.builder.ins().uload8(
                    I64,
                    MemFlags::new(),
                    source_address,
                    Offset32::new(0),
                );
                self.builder.def_var(target, value);
            }
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
            Op::STXRB => {
                // [ref:atomics]: We don't model exclusive access (yet).
                let status_target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => *self.reg_to_var(reg, true),
                    other => panic!("unexpected lhs in {op:?}: {:?}", other),
                };
                let value = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                let mem_start = self.builder.ins().iconst(I64, self.mem_start);
                let target = self.builder.ins().uadd_overflow_trap(
                    target,
                    mem_start,
                    TrapCode::IntegerOverflow,
                );
                self.builder.ins().istore8(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    Offset32::new(0),
                );
                let one = self.builder.ins().iconst(I64, 1);
                self.builder.def_var(status_target, one);
            }
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
                // [ref:FIXME]: What should we do when encountering UDF instructions? Trap?
                return ControlFlow::Break(None);
            }
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

    /// Save state and resolve the next entry block.
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
            // We don't change the lookup_entry_func so just use the function pointer of
            // `lookup_entry` directly.
            //
            // let translate_func = self.builder.ins().load(
            //     self.pointer_type,
            //     MemFlags::trusted().with_vmctx(),
            //     self.machine_ptr,
            //     std::mem::offset_of!(Armv8AMachine, lookup_entry_func) as i32,
            // );
            let translate_func = self
                .builder
                .ins()
                .iconst(I64, lookup_entry as usize as u64 as i64);
            let call = self.builder.ins().call_indirect(
                self.sigref,
                translate_func,
                &[self.jit_ctx_ptr, self.machine_ptr],
            );
            let resolved_entry = self.builder.inst_results(call)[0];
            self.builder.ins().return_(&[resolved_entry]);
        }
    }

    /// Save state but also set `machine.halted` to `true` so that we stop the
    /// emulation instead of fetching the next JIT block.
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
        let true_value = self.builder.ins().iconst(I8, 1);
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

    #[must_use]
    fn unconditional_jump_epilogue(
        &mut self,
        source_instruction: &bad64::Instruction,
        dest_label: Value,
    ) -> ControlFlow<Option<Value>> {
        // [ref:TODO]: Check `dest_label` alignment.
        let pc = self
            .builder
            .ins()
            .iconst(I64, source_instruction.address() as i64);
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            pc,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, prev_pc) as i32,
        );
        self.builder.ins().store(
            MemFlags::trusted().with_vmctx(),
            dest_label,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, pc) as i32,
        );
        ControlFlow::Break(Some(dest_label))
    }
}
