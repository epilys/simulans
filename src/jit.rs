// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Generation of JIT code as translation blocks.

use std::{collections::BTreeSet, ops::ControlFlow};

use bad64::ArrSpec;
use codegen::ir::{
    instructions::BlockArg,
    types::{I128, I16, I16X8, I32, I32X4, I64, I64X2, I8, I8X16},
    Endianness,
};
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module};
use indexmap::IndexMap;
use num_traits::cast::FromPrimitive;

use crate::{
    cpu_state::{ExitRequestID, SysReg, SysRegEncoding},
    exceptions::AccessDescriptor,
    machine::{Armv8AMachine, TranslationBlock, TranslationBlocks},
    memory::{mmu::ResolvedAddress, AccessType, Address, Width},
    tracing,
};

mod arithmetic;
mod memory;
mod simd;
mod sysregs;

use memory::MemOpsTable;
use sysregs::SystemRegister;

const TRUSTED_MEMFLAGS: MemFlags =
    MemFlags::trusted().with_endianness(codegen::ir::Endianness::Little);
const MEMFLAG_LITTLE_ENDIAN: MemFlags = MemFlags::new().with_endianness(Endianness::Little);

enum BlockExit {
    Branch(Value),
    Exception,
}

#[repr(transparent)]
#[derive(Clone, Copy)]
/// An "entry" function for a block.
///
/// It can be either a JIT compiled translation block, or a special emulator
/// function.
pub struct Entry(
    pub for<'a, 'b> extern "C" fn(jit: &'a mut Jit, machine: &'b mut Armv8AMachine) -> Entry,
);

/// Lookup [`machine.pc`] in cached translation blocks
/// ([`Jit::translation_blocks`]).
pub extern "C" fn lookup_block(jit: &mut Jit, machine: &mut Armv8AMachine) -> Entry {
    let virtual_pc: u64 = machine.pc;
    if tracing::event_enabled!(target: tracing::TraceItem::BlockEntry.as_str(), tracing::Level::TRACE)
    {
        crate::tracing::print_registers(machine);
    }
    if machine.cpu_state.exit_request.lock().unwrap().is_some() {
        // Exception raised
        return Entry(lookup_block);
    };
    let Ok(physical_pc) = translate_code_address(machine, virtual_pc) else {
        // Exception raised
        return Entry(lookup_block);
    };
    for addr in machine.invalidate.drain(..) {
        jit.translation_blocks.invalidate(addr);
    }
    if let Some(tb) = jit.translation_blocks.get(&physical_pc.0, &virtual_pc) {
        if jit.single_step != tb.single_step {
            jit.translation_blocks.invalidate(physical_pc.0);
        } else {
            tracing::event!(
                target: tracing::TraceItem::LookupBlock.as_str(),
                tracing::Level::TRACE,
                "re-using cached block {tb:?}",
            );
            if tracing::event_enabled!(target: tracing::TraceItem::InAsm.as_str(), tracing::Level::TRACE)
            {
                if let Ok(code_area) = code_area(machine, virtual_pc, physical_pc) {
                    let input = &code_area[..(tb.end as usize - tb.start as usize + 4)];
                    if let Ok(s) = crate::disas(input, virtual_pc) {
                        tracing::event!(
                            target: tracing::TraceItem::InAsm.as_str(),
                            tracing::Level::TRACE,
                            prev_pc = ?Address(machine.prev_pc),
                            disassembly = %s,
                        );
                    }
                }
            }
            return tb.entry;
        }
    }
    tracing::event!(
        target: tracing::TraceItem::LookupBlock.as_str(),
        tracing::Level::TRACE,
        pc = ?Address(virtual_pc),
        "generating block",
    );

    let machine_addr = std::ptr::addr_of!(*machine).addr();

    let Ok(code_area) = code_area(machine, virtual_pc, physical_pc) else {
        // Exception raised
        return Entry(lookup_block);
    };

    let block = match JitContext::new(machine_addr, &machine.debug_monitor.hw_breakpoints, jit)
        .compile(code_area, virtual_pc, physical_pc.0)
    {
        Ok(b) => b,
        err @ Err(_) => {
            eprintln!("Could not compile pc={virtual_pc:#x}");
            err.unwrap()
        }
    };
    if tracing::event_enabled!(target: tracing::TraceItem::InAsm.as_str(), tracing::Level::TRACE) {
        let input = &code_area[..(block.end as usize - block.start as usize + 4)];
        if let Ok(s) = crate::disas(input, virtual_pc) {
            tracing::event!(
                target: tracing::TraceItem::InAsm.as_str(),
                tracing::Level::TRACE,
                prev_pc = ?Address(machine.prev_pc),
                disassembly = %s,
            );
        }
    }
    tracing::event!(
        target: tracing::TraceItem::LookupBlock.as_str(),
        tracing::Level::TRACE,
        block = ?block,
        "returning generated block",
    );
    let next_entry = block.entry;
    jit.translation_blocks.insert(block);

    next_entry
}

pub fn translate_code_address(
    machine: &Armv8AMachine,
    pc: u64,
) -> Result<Address, Box<dyn std::error::Error>> {
    let accessdesc = AccessDescriptor {
        read: true,
        ..AccessDescriptor::new(true, &machine.cpu_state.PSTATE(), AccessType::IFETCH)
    };
    match machine.translate_address(Address(pc), Address(pc), true, accessdesc) {
        Ok(ResolvedAddress {
            mem_region: _,
            address_inside_region: _,
            physical,
        }) => Ok(physical),
        Err(exit_request) => {
            *machine.cpu_state.exit_request.lock().unwrap() = Some(exit_request);
            Err(format!(
                "Received program counter {} which is unmapped in physical memory.",
                Address(pc),
            )
            .into())
        }
    }
}

fn code_area(
    machine: &Armv8AMachine,
    virtual_pc: u64,
    physical_pc: Address,
) -> Result<&[u8], Box<dyn std::error::Error>> {
    let mem_region = machine.memory.find_region(physical_pc).unwrap();
    let pc_offset = physical_pc.0 - mem_region.phys_offset.0;
    let Some(mmapped_region) = mem_region.as_mmap() else {
        return Err(format!(
            "Received program counter {} which is mapped in device memory.",
            Address(virtual_pc),
        )
        .into());
    };
    Ok(&mmapped_region.as_ref()[pc_offset.try_into().unwrap()..])
}

pub struct Jit {
    pub translation_blocks: TranslationBlocks,
    pub single_step: bool,
}

impl Jit {
    pub fn new() -> Self {
        Self {
            translation_blocks: TranslationBlocks::new(),
            single_step: false,
        }
    }
}

impl Default for Jit {
    fn default() -> Self {
        Self::new()
    }
}

/// JIT context/builder used to disassemble code and JIT compile it.
pub struct JitContext<'j> {
    hw_breakpoints: &'j BTreeSet<Address>,
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
    single_step: bool,
    /// Address of [`Pin<Box<Armv8AMachine>>`] in memory.
    machine_addr: usize,
}

impl<'j> JitContext<'j> {
    /// Returns a new [`JitContext`].
    pub fn new(machine_addr: usize, hw_breakpoints: &'j BTreeSet<Address>, jit: &'j Jit) -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "speed").unwrap();
        flag_builder.set("regalloc_checker", "false").unwrap();
        flag_builder.set("enable_verifier", "true").unwrap();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder
            .set("enable_llvm_abi_extensions", "true")
            .unwrap();

        let module = JITModule::new(JITBuilder::with_isa(
            cranelift_native::builder()
                .unwrap_or_else(|msg| {
                    panic!("host machine is not supported: {}", msg);
                })
                .finish(settings::Flags::new(flag_builder))
                .unwrap(),
            cranelift_module::default_libcall_names(),
        ));
        Self {
            hw_breakpoints,
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            module,
            single_step: jit.single_step,
            machine_addr,
        }
    }

    /// Performs compilation of a block starting at `program_counter`] and
    /// returns an [`Entry`] for it.
    pub fn compile(
        mut self,
        code_area: &[u8],
        program_counter: u64,
        physical_pc: u64,
    ) -> Result<TranslationBlock, Box<dyn std::error::Error>> {
        tracing::event!(
            target: tracing::TraceItem::Jit.as_str(),
            tracing::Level::TRACE,
            pc = ?Address(program_counter),
            "compiling",
        );
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
        let last_pc = self.translate(code_area, program_counter)?;

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
        //     tracing::trace!("cranelift IR for translation block at pc={pc:#x}:");
        //     tracing::trace!("{}", self.ctx.func);
        //     tracing::trace!("Native generated code for translation block at
        // pc={pc:#x}:");     tracing::trace!(
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
        let entry = unsafe {
            std::mem::transmute::<*const u8, Entry>(self.module.get_finalized_function(id))
        };
        Ok(TranslationBlock {
            start: physical_pc,
            end: (last_pc - program_counter) + physical_pc,
            virtual_addr: program_counter,
            entry,
            single_step: self.single_step,
            ctx: self.module,
        })
    }

    /// Translate instructions starting from address `program_counter`.
    fn translate(
        &mut self,
        code_area: &[u8],
        program_counter: u64,
    ) -> Result<u64, Box<dyn std::error::Error>> {
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        let memops_table = MemOpsTable::new(&self.module, &mut builder);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        builder.append_block_params_for_function_params(entry_block);

        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        let machine_ptr = builder.ins().iconst(
            self.module.target_config().pointer_type(),
            self.machine_addr as i64,
        );
        let set_exception_func = builder.ins().iconst(
            I64,
            crate::machine::helper_set_exit_request as usize as u64 as i64,
        );

        let mut trans = BlockTranslator {
            address: program_counter,
            write_to_sysreg: false,
            write_to_simd: false,
            pointer_type: self.module.target_config().pointer_type(),
            memops_table,
            machine_ptr,
            set_exception_func,
            builder,
            module: &self.module,
            registers: IndexMap::new(),
            sys_registers: IndexMap::new(),
            loopback_blocks: IndexMap::default(),
            writebacks: vec![],
        };
        // Emit code to load register values into variables.
        trans.load_cpu_state(true);
        if !self.single_step {
            for ins in bad64::disasm(code_area, program_counter) {
                let Ok(ins) = ins else {
                    break;
                };
                use bad64::Op;
                let label_idx = match ins.op() {
                    Op::CBNZ | Op::CBZ => 1,
                    Op::TBNZ | Op::TBZ => 2,
                    Op::B_AL
                    | Op::B_CC
                    | Op::B_CS
                    | Op::B_EQ
                    | Op::B_GE
                    | Op::B_GT
                    | Op::B_HI
                    | Op::B_LE
                    | Op::B_LS
                    | Op::B_LT
                    | Op::B_MI
                    | Op::B_NE
                    | Op::B_NV
                    | Op::B_PL
                    | Op::B_VC
                    | Op::B_VS => 0,
                    Op::BRK
                    | Op::HVC
                    | Op::SVC
                    | Op::WFI
                    | Op::WFE
                    | Op::B
                    | Op::BR
                    | Op::BL
                    | Op::BLR
                    | Op::RET
                    | Op::UDF
                    | Op::YIELD
                    | Op::ISB
                    | Op::ERET => break,
                    _ => continue,
                };

                let label = match ins.operands()[label_idx] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    _ => unreachable!(),
                };
                if label >= program_counter && label < ins.address() {
                    let ins_block = trans.builder.create_block();
                    trans.loopback_blocks.insert(label, ins_block);
                }
            }
        }
        let mut next_pc = None;
        let mut last_pc = program_counter;
        // Translate each decoded instruction
        let mut decoded_iter = bad64::disasm(code_area, program_counter);

        let mut count = 1;
        if let Some(first) = decoded_iter.next() {
            let first = first.map_err(|err| format!("Error decoding instruction: {}", err))?;
            last_pc = first.address();
            tracing::event!(
                target: tracing::TraceItem::Jit.as_str(),
                tracing::Level::TRACE,
                pc = ?Address(first.address()),
                "{first:?}",
            );
            if let ControlFlow::Break(jump_pc) = trans.translate_instruction(&first) {
                next_pc = jump_pc;
            } else if self.single_step {
                next_pc = Some(BlockExit::Branch(
                    trans.builder.ins().iconst(I64, (last_pc + 4) as i64),
                ));
            } else {
                for insn in decoded_iter {
                    match insn {
                        Ok(insn) => {
                            tracing::event!(
                                target: tracing::TraceItem::Jit.as_str(),
                                tracing::Level::TRACE,
                                pc = ?Address(insn.address()),
                                "{insn:?}",
                            );
                            if !self.hw_breakpoints.is_empty()
                                && self.hw_breakpoints.contains(&Address(insn.address()))
                            {
                                next_pc = Some(BlockExit::Branch(
                                    trans.builder.ins().iconst(I64, insn.address() as i64),
                                ));
                                break;
                            }
                            last_pc = insn.address();
                            if let ControlFlow::Break(jump_pc) = trans.translate_instruction(&insn)
                            {
                                next_pc = jump_pc;
                                break;
                            }
                            count += 1;
                            if count == 12_000 {
                                next_pc = Some(BlockExit::Branch(
                                    trans.builder.ins().iconst(I64, insn.address() as i64 + 4),
                                ));
                                break;
                            }
                        }
                        Err(err) => {
                            return Err(format!("Error decoding instruction: {}", err).into());
                        }
                    }
                }
            }
        }
        let block_exit = next_pc.unwrap_or_else(|| {
            // We are out of code?
            _ = trans.throw_undefined();
            BlockExit::Exception
        });
        trans.direct_exit(block_exit);
        let BlockTranslator {
            mut builder,
            loopback_blocks,
            writebacks,
            ..
        } = trans;
        for (_, block) in loopback_blocks.into_iter() {
            builder.seal_block(block);
        }
        // abort if writebacks is not empty, that means we have forgotten to perform
        // them in `translate_instruction`.
        assert!(writebacks.is_empty(), "{writebacks:?}");

        // Tell the builder we're done with this block (function in Cranelift terms).
        builder.finalize();
        Ok(last_pc)
    }
}

/// In-progress state of translating instructions into Cranelift IR.
struct BlockTranslator<'a> {
    address: u64,
    write_to_sysreg: bool,
    write_to_simd: bool,
    builder: FunctionBuilder<'a>,
    module: &'a JITModule,
    machine_ptr: Value,
    set_exception_func: Value,
    pointer_type: Type,
    memops_table: MemOpsTable,
    registers: IndexMap<bad64::Reg, Variable>,
    sys_registers: IndexMap<SysReg, Variable>,
    loopback_blocks: IndexMap<u64, Block>,
    /// Register write backs (load/store pre/post index increments)
    ///
    /// They are performed after the load/store are finished and any destination
    /// registers (for stores) are written. A data abort might interrupt
    /// this, so we save them here and do the write backs on success.
    writebacks: Vec<(bad64::Reg, Value)>,
}

#[derive(Debug, Copy, Clone)]
struct TypedRegisterView {
    var: Variable,
    width: Width,
    extend_to: Option<Width>,
    element: Option<ArrSpec>,
}

#[derive(Debug)]
struct TypedValue {
    width: Width,
    value: Value,
}

#[inline]
fn is_vector(reg: &bad64::Reg) -> bool {
    use bad64::Reg;
    let reg = *reg as u32;
    ((Reg::V0 as u32)..=(Reg::Q31 as u32)).contains(&reg)
}

impl BlockTranslator<'_> {
    fn branch_if_non_zero(&mut self, test_value: Value, label: u64) {
        let branch_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(test_value, branch_block, &[], merge_block, &[]);
        self.builder.switch_to_block(branch_block);
        self.builder.seal_block(branch_block);
        if let Some(loopback_block) = self.loopback_blocks.get(&label).copied() {
            self.builder.ins().jump(loopback_block, &[]);
        } else {
            let label_value = self.builder.ins().iconst(I64, label as i64);
            self.direct_exit(BlockExit::Branch(label_value));
        }
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
    }

    fn translate_operand_extended(&mut self, operand: &bad64::Operand, extend_to: Width) -> Value {
        match operand {
            bad64::Operand::ShiftReg { ref reg, shift } => {
                use bad64::Shift;

                let value = self.reg_to_value(reg, None);
                let width = self.operand_width(operand);
                match shift {
                    Shift::LSL(_)
                    | Shift::LSR(_)
                    | Shift::ASR(_)
                    | Shift::ROR(_)
                    | Shift::MSL(_) => self.translate_operand(operand),
                    Shift::UXTW(uxtw) => {
                        // [ref:verify_implementation]
                        let value = if extend_to > width {
                            self.builder.ins().uextend(extend_to.into(), value)
                        } else {
                            value
                        };
                        if *uxtw == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*uxtw))
                        }
                    }
                    Shift::SXTW(sxtw) => {
                        // [ref:verify_implementation]
                        let value = if extend_to > width {
                            self.builder.ins().sextend(extend_to.into(), value)
                        } else {
                            value
                        };
                        if *sxtw == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*sxtw))
                        }
                    }
                    Shift::SXTX(sxtx) => {
                        let value = if extend_to > width {
                            self.builder.ins().sextend(extend_to.into(), value)
                        } else {
                            value
                        };
                        if *sxtx == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*sxtx))
                        }
                    }
                    Shift::UXTX(uxtx) => {
                        let value = if extend_to > width {
                            self.builder.ins().uextend(extend_to.into(), value)
                        } else {
                            value
                        };
                        if *uxtx == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*uxtx))
                        }
                    }
                    Shift::SXTB(sxtb) => {
                        // [ref:verify_implementation]
                        let value = self.builder.ins().ireduce(I8, value);
                        let value = self.builder.ins().sextend(extend_to.into(), value);
                        if *sxtb == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*sxtb))
                        }
                    }
                    Shift::SXTH(sxth) => {
                        // [ref:verify_implementation]
                        let value = self.builder.ins().ireduce(I16, value);
                        let value = self.builder.ins().sextend(extend_to.into(), value);
                        if *sxth == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*sxth))
                        }
                    }
                    Shift::UXTH(uxth) => {
                        // [ref:verify_implementation]
                        let value = self.builder.ins().ireduce(I16, value);
                        let value = self.builder.ins().uextend(extend_to.into(), value);
                        if *uxth == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*uxth))
                        }
                    }
                    Shift::UXTB(uxtb) => {
                        // [ref:verify_implementation]
                        let value = self.builder.ins().ireduce(I8, value);
                        let value = self.builder.ins().uextend(extend_to.into(), value);
                        if *uxtb == 0 {
                            value
                        } else {
                            self.builder.ins().ishl_imm(value, i64::from(*uxtb))
                        }
                    }
                }
            }
            _ => self.translate_operand(operand),
        }
    }

    fn translate_operand(&mut self, operand: &bad64::Operand) -> Value {
        use bad64::{Imm, Operand};

        match operand {
            Operand::Reg { ref reg, arrspec } => self.reg_to_value(reg, *arrspec),
            Operand::ShiftReg { ref reg, shift } => {
                use bad64::Shift;

                let value = self.reg_to_value(reg, None);
                match shift {
                    Shift::LSL(lsl) => self.builder.ins().ishl_imm(value, i64::from(*lsl)),
                    Shift::LSR(lsr) => self.builder.ins().ushr_imm(value, i64::from(*lsr)),
                    Shift::ASR(asr) => {
                        // [ref:verify_implementation]
                        self.builder.ins().sshr_imm(value, i64::from(*asr))
                    }
                    Shift::ROR(ror) => self.builder.ins().rotr_imm(value, i64::from(*ror)),
                    Shift::MSL(lsl) => {
                        let val = self.builder.ins().ishl_imm(value, i64::from(*lsl));
                        self.builder.ins().bor_imm(val, 2_i64.pow(*lsl) - 1)
                    }
                    Shift::UXTW(_)
                    | Shift::SXTW(_)
                    | Shift::SXTX(_)
                    | Shift::UXTX(_)
                    | Shift::SXTB(_)
                    | Shift::SXTH(_)
                    | Shift::UXTH(_)
                    | Shift::UXTB(_) => {
                        panic!()
                    }
                }
            }
            Operand::MemPreIdx { ref reg, imm } => {
                let reg_val = self.reg_to_value(reg, None);
                let value = match imm {
                    Imm::Unsigned(imm) => self.builder.ins().iadd_imm(reg_val, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iadd_imm(reg_val, *imm),
                };
                self.writebacks.push((*reg, value));
                value
            }
            Operand::MemPostIdxImm { ref reg, imm } => {
                let reg_val = self.reg_to_value(reg, None);
                let post_value = match imm {
                    Imm::Unsigned(imm) => self.builder.ins().iadd_imm(reg_val, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iadd_imm(reg_val, *imm),
                };
                self.writebacks.push((*reg, post_value));
                reg_val
            }
            Operand::Imm64 { imm, shift } => {
                let const_value = match imm {
                    Imm::Unsigned(imm) => self.builder.ins().iconst(I64, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iconst(I64, *imm),
                };
                match shift {
                    None => const_value,
                    Some(bad64::Shift::LSL(lsl)) => {
                        self.builder.ins().ishl_imm(const_value, i64::from(*lsl))
                    }
                    Some(bad64::Shift::MSL(lsl)) => {
                        let val = self.builder.ins().ishl_imm(const_value, i64::from(*lsl));
                        self.builder.ins().bor_imm(val, 2_i64.pow(*lsl) - 1)
                    }
                    other => unimplemented!("unimplemented shift {other:?}"),
                }
            }
            Operand::Imm32 { imm, shift } => {
                let const_value = match imm {
                    Imm::Unsigned(imm) => self.builder.ins().iconst(I32, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iconst(I32, *imm),
                };
                match shift {
                    None => const_value,
                    Some(bad64::Shift::LSL(lsl)) => {
                        self.builder.ins().ishl_imm(const_value, i64::from(*lsl))
                    }
                    Some(bad64::Shift::MSL(lsl)) => {
                        let val = self.builder.ins().ishl_imm(const_value, i64::from(*lsl));
                        self.builder.ins().bor_imm(val, 2_i64.pow(*lsl) - 1)
                    }
                    other => unimplemented!("unimplemented shift {other:?}"),
                }
            }
            Operand::MemReg(reg) => self.reg_to_value(reg, None),
            Operand::MemOffset {
                reg,
                offset,
                mul_vl: false,
                arrspec: None,
            } => {
                let reg_val = self.reg_to_value(reg, None);
                match offset {
                    Imm::Unsigned(imm) => self.builder.ins().iadd_imm(reg_val, *imm as i64),
                    Imm::Signed(imm) => self.builder.ins().iadd_imm(reg_val, *imm),
                }
            }
            Operand::Label(Imm::Unsigned(imm)) => self.builder.ins().iconst(I64, *imm as i64),
            Operand::Label(Imm::Signed(imm)) => self.builder.ins().iconst(I64, *imm),
            Operand::ImplSpec { o0, o1, cm, cn, o2 } => {
                let (o0, o1, cm, cn, o2) = (*o0, *o1, *cm, *cn, *o2);
                self.read_sysreg(&SysRegEncoding { o0, o1, cm, cn, o2 }.into())
            }
            Operand::SysReg(reg) => self.read_sysreg(&reg.into()),
            Operand::MemExt {
                regs: [ref address_reg, ref offset_reg],
                shift,
                arrspec: None,
            } => {
                let address = self.reg_to_value(address_reg, None);
                let offset = self.reg_to_value(offset_reg, None);
                let offset = match shift {
                    None => offset,
                    Some(bad64::Shift::LSL(ref lsl)) => {
                        self.builder.ins().ishl_imm(offset, i64::from(*lsl))
                    }
                    Some(bad64::Shift::MSL(ref lsl)) => {
                        let val = self.builder.ins().ishl_imm(offset, i64::from(*lsl));
                        self.builder.ins().bor_imm(val, 2_i64.pow(*lsl) - 1)
                    }
                    Some(bad64::Shift::UXTW(ref uxtw)) => {
                        let addr_width = self.reg_width(address_reg);
                        let offset_width = self.reg_width(offset_reg);
                        let offset = if addr_width > offset_width {
                            self.builder.ins().uextend(addr_width.into(), offset)
                        } else {
                            offset
                        };
                        if *uxtw == 0 {
                            offset
                        } else {
                            self.builder.ins().ishl_imm(offset, i64::from(*uxtw))
                        }
                    }
                    Some(bad64::Shift::SXTW(ref sxtw)) => {
                        let addr_width = self.reg_width(address_reg);
                        let offset_width = self.reg_width(offset_reg);
                        let offset = if addr_width > offset_width {
                            self.builder.ins().sextend(addr_width.into(), offset)
                        } else {
                            offset
                        };
                        if *sxtw == 0 {
                            offset
                        } else {
                            self.builder.ins().ishl_imm(offset, i64::from(*sxtw))
                        }
                    }
                    other => unimplemented!("unimplemented shift {other:?}"),
                };
                self.builder.ins().iadd(address, offset)
            }
            other => unimplemented!("unexpected rhs in translate_operand: {:?}", other),
        }
    }

    #[cold]
    fn simd_reg_to_var(
        &mut self,
        reg: &bad64::Reg,
        element: Option<ArrSpec>,
        write: bool,
    ) -> TypedRegisterView {
        use bad64::Reg;

        self.write_to_simd |= write;

        let reg_no = *reg as u32;
        let (i, width) = if ((Reg::V0 as u32)..=(Reg::V31 as u32)).contains(&reg_no) {
            (reg_no - (Reg::V0 as u32), Width::_128)
        } else if ((Reg::Q0 as u32)..=(Reg::Q31 as u32)).contains(&reg_no) {
            // Registers Q0-Q31 map directly to registers V0-V31.
            (reg_no - (Reg::Q0 as u32), Width::_128)
        } else if ((Reg::D0 as u32)..=(Reg::D31 as u32)).contains(&reg_no) {
            (reg_no - (Reg::D0 as u32), Width::_64)
        } else if ((Reg::S0 as u32)..=(Reg::S31 as u32)).contains(&reg_no) {
            // 32 bits
            (reg_no - (Reg::S0 as u32), Width::_32)
        } else if ((Reg::H0 as u32)..=(Reg::H31 as u32)).contains(&reg_no) {
            // 16 bits
            (reg_no - (Reg::H0 as u32), Width::_16)
        } else {
            // 8 bits
            assert!(((Reg::B0 as u32)..=(Reg::B31 as u32)).contains(&reg_no));
            (reg_no - (Reg::B0 as u32), Width::_8)
        };
        let reg = Reg::from_u32(i + Reg::V0 as u32).unwrap();
        TypedRegisterView {
            var: self.registers[&reg],
            width,
            extend_to: if matches!(width, Width::_128) {
                None
            } else {
                Some(Width::_128)
            },
            element,
        }
    }

    #[inline]
    fn reg_to_var(
        &mut self,
        reg: &bad64::Reg,
        element: Option<ArrSpec>,
        write: bool,
    ) -> TypedRegisterView {
        use bad64::Reg;

        if is_vector(reg) {
            return self.simd_reg_to_var(reg, element, write);
        }

        if reg.is_sve() {
            todo!();
        }

        if reg.is_pred() {
            todo!();
        }
        assert!(element.is_none());

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
            Reg::WZR => {
                return TypedRegisterView {
                    var: self.registers[&Reg::XZR],
                    width: Width::_32,
                    extend_to: Some(Width::_64),
                    element,
                }
            }
            _ => {
                return TypedRegisterView {
                    var: self.registers[reg],
                    width: Width::_64,
                    extend_to: None,
                    element,
                };
            }
        };
        TypedRegisterView {
            var: self.registers[&reg_64],
            width: Width::_32,
            extend_to: Some(Width::_64),
            element,
        }
    }

    #[cold]
    fn simd_reg_view_to_value(
        &mut self,
        reg: TypedRegisterView,
        element: Option<ArrSpec>,
    ) -> Value {
        let mut value = self.builder.use_var(reg.var);

        match reg.width {
            Width::_128 => match element {
                None | Some(ArrSpec::OneDouble(None)) => value,
                Some(ArrSpec::OneDouble(Some(lane))) => {
                    value = self
                        .builder
                        .ins()
                        .bitcast(I64X2, MEMFLAG_LITTLE_ENDIAN, value);
                    value = self.builder.ins().extractlane(value, lane as u8);
                    self.builder
                        .ins()
                        .bitcast(I64, MEMFLAG_LITTLE_ENDIAN, value)
                }
                Some(ArrSpec::EightBytes(None)) => value,
                Some(ArrSpec::TwoDoubles(None)) => value,
                Some(ArrSpec::OneSingle(Some(lane))) => {
                    // [ref:cranelift_ice]: I32X2 would be more appropriate but cranelift ICEs with
                    // Compilation(Unsupported("should be implemented in ISLE: inst = `v164 =
                    // extractlane.i32x2 v163, 0`, type = `Some(types::I32)`"))
                    value = self
                        .builder
                        .ins()
                        .bitcast(I32X4, MEMFLAG_LITTLE_ENDIAN, value);
                    value = self.builder.ins().extractlane(value, lane as u8);
                    self.builder
                        .ins()
                        .bitcast(I32, MEMFLAG_LITTLE_ENDIAN, value)
                }
                Some(ArrSpec::SixteenBytes(None)) => value,
                Some(ArrSpec::OneHalf(Some(lane))) => {
                    value = self
                        .builder
                        .ins()
                        .bitcast(I16X8, MEMFLAG_LITTLE_ENDIAN, value);
                    value = self.builder.ins().extractlane(value, lane as u8);
                    self.builder
                        .ins()
                        .bitcast(I16, MEMFLAG_LITTLE_ENDIAN, value)
                }
                other => unreachable!("{other:?}"),
            },
            Width::_64 => self.builder.ins().ireduce(I64, value),
            Width::_32 => self.builder.ins().ireduce(I32, value),
            Width::_16 => self.builder.ins().ireduce(I16, value),
            Width::_8 => self.builder.ins().ireduce(I8, value),
        }
    }

    #[cold]
    fn simd_reg_to_value(&mut self, reg: &bad64::Reg, element: Option<ArrSpec>) -> Value {
        let reg = self.simd_reg_to_var(reg, element, false);
        self.simd_reg_view_to_value(reg, element)
    }

    #[inline]
    fn reg_to_value(&mut self, reg: &bad64::Reg, element: Option<ArrSpec>) -> Value {
        use bad64::Reg;

        if is_vector(reg) {
            return self.simd_reg_to_value(reg, element);
        }

        if reg.is_sve() {
            todo!();
        }

        if reg.is_pred() {
            todo!();
        }

        assert!(element.is_none());

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
            Reg::WZR => {
                return self.builder.ins().iconst(I32, 0);
            }
            Reg::XZR => {
                return self.builder.ins().iconst(I64, 0);
            }
            _ => {
                let var = &self.registers[reg];
                return self.builder.use_var(*var);
            }
        };
        // Reads from W registers ignore the higher 32 bits of the corresponding X
        // register and leave them unchanged.
        let value = self.builder.use_var(self.registers[&reg_64]);
        self.builder.ins().ireduce(I32, value)
    }

    fn reg_width(&self, reg: &bad64::Reg) -> Width {
        use bad64::Reg;

        let reg_no = *reg as u32;

        if is_vector(reg) {
            if ((Reg::V0 as u32)..=(Reg::V31 as u32)).contains(&reg_no)
                || ((Reg::Q0 as u32)..=(Reg::Q31 as u32)).contains(&reg_no)
            {
                Width::_128
            } else if ((Reg::D0 as u32)..=(Reg::D31 as u32)).contains(&reg_no) {
                Width::_64
            } else if ((Reg::S0 as u32)..=(Reg::S31 as u32)).contains(&reg_no) {
                Width::_32
            } else if ((Reg::H0 as u32)..=(Reg::H31 as u32)).contains(&reg_no) {
                Width::_16
            } else {
                Width::_8
            }
        } else if ((Reg::W0 as u32)..=(Reg::W30 as u32)).contains(&reg_no)
            || matches!(reg, Reg::WSP | Reg::WZR)
        {
            Width::_32
        } else {
            Width::_64
        }
    }

    fn operand_width(&self, operand: &bad64::Operand) -> Width {
        use bad64::Operand;

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
        self.reg_width(reg)
    }

    #[inline]
    fn store_pc(&mut self, pc_value: Option<Value>) {
        let pc_value =
            pc_value.unwrap_or_else(|| self.builder.ins().iconst(I64, self.address as i64));
        self.builder.ins().store(
            TRUSTED_MEMFLAGS,
            pc_value,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, pc) as i32,
        );
    }

    /// JIT a single instruction.
    fn translate_instruction(
        &mut self,
        instruction: &bad64::Instruction,
    ) -> ControlFlow<Option<BlockExit>> {
        use bad64::Op;

        self.address = instruction.address();
        if let Some(loopback_block) = self.loopback_blocks.get(&instruction.address()).copied() {
            self.builder.ins().jump(loopback_block, &[]);
            self.builder.switch_to_block(loopback_block);
        }
        if cfg!(feature = "accurate-pc") {
            self.store_pc(None);
        }
        let op = instruction.op();

        macro_rules! write_to_register {
            ($target:expr, $val:expr$(,)?) => {{
                let val: TypedValue = $val;
                let target: TypedRegisterView = $target;

                let mut value = val.value;

                let mut current_width = val.width;

                if let Some(extend_to) = target.extend_to {
                    if extend_to > current_width {
                        value = self.builder.ins().uextend(extend_to.into(), value);
                        current_width = extend_to;
                    }
                }
                if target.width > current_width {
                    value = self.builder.ins().uextend(target.width.into(), value);
                }
                self.def_view(&target, value);
            }};
            (signed $target:expr, $val:expr$(,)?) => {{
                let val: TypedValue = $val;
                let target: TypedRegisterView = $target;

                let mut value = val.value;

                let mut current_width = val.width;

                if target.width > current_width {
                    value = self.builder.ins().sextend(target.width.into(), value);
                    current_width = target.width;
                }
                if let Some(extend_to) = target.extend_to {
                    if extend_to > current_width {
                        value = self.builder.ins().uextend(extend_to.into(), value);
                    }
                }
                self.def_view(&target, value);
            }};
        }
        // Common implementations
        macro_rules! b_cnd {
            ($cnd:ident) => {{
                let result = self.condition_holds(bad64::Condition::$cnd);
                let result = self.builder.ins().uextend(I64, result);
                let label = match instruction.operands()[0] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => panic!(
                        "unexpected branch address in {op:?}: {:?}. Instruction: {instruction:?}",
                        other
                    ),
                };
                self.branch_if_non_zero(result, label);
            }};
        }
        macro_rules! ands {
            ($a:expr, $b:expr) => {{
                let result = self.builder.ins().band($a, $b);
                let n = self
                    .builder
                    .ins()
                    .icmp_imm(IntCC::SignedLessThan, result, 0);
                let n = self.builder.ins().uextend(I64, n);
                let z = self.builder.ins().icmp_imm(IntCC::Equal, result, 0);
                let z = self.builder.ins().uextend(I64, z);
                let empty = self.builder.ins().iconst(I64, 0);
                (result, [n, z, empty, empty])
            }};
        }
        macro_rules! crc_byte {
            ($is_c:expr, $acc:expr, $byte:expr) => {{
                if $is_c {
                    crc_byte!(_inner $acc, $byte, arithmetic::CRC32C_TABLE.as_ptr())
                } else {
                    crc_byte!(_inner $acc, $byte, arithmetic::CRC32_TABLE.as_ptr())
                }
            }};
            (_inner $acc:expr, $byte:expr, $table:expr) => {{
                // [ref:TODO]: this performs precomputed table lookup, but it'd be faster to
                // perform polynomial modulus over {0,1} directly
                let table = $table as usize as i64;
                let acc: Value = $acc;
                let byte: Value = $byte;
                let byte = self.builder.ins().ireduce(I8, byte);
                // Calculate table index: (acc & 0xff) ^ byte
                let index = {
                    let index = self.builder.ins().band_imm(acc, 0xff);
                    let byte = self.builder.ins().uextend(I32, byte);
                    let index = self.builder.ins().bxor(index, byte);
                    let index = self
                        .builder
                        .ins()
                        .imul_imm(index, std::mem::size_of::<u32>() as i64);
                    self.builder
                        .ins()
                        .uextend(self.module.target_config().pointer_type(), index)
                };
                let table_ptr = self
                    .builder
                    .ins()
                    .iadd_imm(index, table);
                let value = self
                    .builder
                    .ins()
                    .load(I32, TRUSTED_MEMFLAGS, table_ptr, 0);
                // ((acc >> 8) ^ arithmetic::CRC32_TABLE[((acc & 0xff) ^ byte as u32) as usize])
                let acc = self.builder.ins().ushr_imm(acc, 8);
                self.builder.ins().bxor(acc, value)
            }};
        }
        macro_rules! condition_holds {
            ($cond:expr) => {{
                let result = self.condition_holds($cond);
                self.builder.ins().uextend(I64, result)
            }};
            (invert $cond:expr) => {{
                let result = self.condition_holds($cond);
                let result = self.builder.ins().icmp_imm(IntCC::Equal, result, 0);
                self.builder.ins().uextend(I64, result)
            }};
        }
        macro_rules! cs {
            (inc Rd = $Rd:expr, Rn = $Rn:expr, Rm = $Rm:expr, cond = $cond:expr, width = $width:expr) => {{
                let cond = $cond;
                let true_block = self.builder.create_block();
                let false_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, $width.into());
                self.builder
                    .ins()
                    .brif(cond, true_block, &[], false_block, &[]);
                self.builder.switch_to_block(true_block);
                self.builder.seal_block(true_block);
                self.builder.ins().jump(merge_block, &[BlockArg::from($Rn)]);

                self.builder.switch_to_block(false_block);
                self.builder.seal_block(false_block);
                let incremented_value = self.builder.ins().iadd_imm($Rm, 1);
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(incremented_value)]);

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                let phi = self.builder.block_params(merge_block)[0];
                write_to_register!(
                    $Rd,
                    TypedValue {
                        value: phi,
                        width: $width,
                    },
                );
                phi
            }};
            (inv Rd = $Rd:expr, Rn = $Rn:expr, Rm = $Rm:expr, cond = $cond:expr, width = $width:expr) => {{
                let cond = $cond;
                let true_block = self.builder.create_block();
                let false_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, $width.into());
                self.builder
                    .ins()
                    .brif(cond, true_block, &[], false_block, &[]);
                self.builder.switch_to_block(true_block);
                self.builder.seal_block(true_block);
                self.builder.ins().jump(merge_block, &[BlockArg::from($Rn)]);

                self.builder.switch_to_block(false_block);
                self.builder.seal_block(false_block);
                let inverted_value = self.builder.ins().bnot($Rm);
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(inverted_value)]);

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                let phi = self.builder.block_params(merge_block)[0];
                write_to_register!(
                    $Rd,
                    TypedValue {
                        value: phi,
                        width: $width,
                    },
                );
                phi
            }};
            (neg Rd = $Rd:expr, Rn = $Rn:expr, Rm = $Rm:expr, cond = $cond:expr, width = $width:expr) => {{
                let cond = $cond;
                let true_block = self.builder.create_block();
                let false_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, $width.into());
                self.builder
                    .ins()
                    .brif(cond, true_block, &[], false_block, &[]);
                self.builder.switch_to_block(true_block);
                self.builder.seal_block(true_block);
                self.builder.ins().jump(merge_block, &[BlockArg::from($Rn)]);

                self.builder.switch_to_block(false_block);
                self.builder.seal_block(false_block);
                let neg_value = self.builder.ins().bnot($Rm);
                let neg_value = self.builder.ins().iadd_imm(neg_value, 1);
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(neg_value)]);

                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                let phi = self.builder.block_params(merge_block)[0];
                write_to_register!(
                    $Rd,
                    TypedValue {
                        value: phi,
                        width: $width,
                    },
                );
                phi
            }};
        }
        /// Sign-extend a bitfield value
        /// (which might be any MSB depending on the bitfield's width)
        // Is there a cleaner way to do this?
        macro_rules! sign_extend_bitfield {
            ($val:expr, $msb:expr, $width:expr) => {{
                let msb = self
                    .builder
                    .ins()
                    .band_imm($val, 2_i64.pow($msb as u32 - 1));
                let is_one =
                    self.builder
                        .ins()
                        .icmp_imm(cranelift::prelude::IntCC::NotEqual, msb, 0);
                let is_one = self.builder.ins().uextend($width.into(), is_one);
                let mask = self.builder.ins().iconst($width.into(), 0);
                let mask = self.builder.ins().bnot(mask);
                let mask = self
                    .builder
                    .ins()
                    .band_imm(mask, !(2_i64.pow($msb as u32) - 1));
                let mask = self.builder.ins().imul(mask, is_one);

                self.builder.ins().bor($val, mask)
            }};
        }
        macro_rules! get_destination_register {
            () => {{
                get_destination_register!(0)
            }};
            ($idx:expr) => {{
                match instruction.operands()[$idx] {
                    bad64::Operand::Reg { ref reg, arrspec } => self.reg_to_var(reg, arrspec, true),
                    other => unexpected_operand!(other),
                }
            }};
        }
        macro_rules! monitor {
            (load_excl $addr:expr) => {{
                let addr = $addr;
                let sigref = {
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(self.pointer_type));
                    sig.params.push(AbiParam::new(I64));
                    self.builder.import_signature(sig)
                };
                let load_excl = self
                    .builder
                    .ins()
                    .iconst(I64, crate::cpu_state::load_excl as usize as u64 as i64);
                let monitor_addr = self.builder.ins().iadd_imm(
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, cpu_state.monitor) as i64,
                );
                let call =
                    self.builder
                        .ins()
                        .call_indirect(sigref, load_excl, &[monitor_addr, addr]);
                _ = self.builder.inst_results(call);
            }};
            (store_excl $addr:expr, $status_target:expr, $($stores:tt)*) => {{
                let addr = $addr;
                let status_target = $status_target;
                let sigref = {
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(self.pointer_type));
                    sig.params.push(AbiParam::new(I64));
                    sig.returns.push(AbiParam::new(I8));
                    self.builder.import_signature(sig)
                };
                let store_excl = self
                    .builder
                    .ins()
                    .iconst(I64, crate::cpu_state::store_excl as usize as u64 as i64);
                let monitor_addr = self.builder.ins().iadd_imm(
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, cpu_state.monitor) as i64,
                );
                let call = self.builder
                    .ins()
                    .call_indirect(sigref, store_excl, &[monitor_addr, addr]);
                let is_failure = self.builder.inst_results(call)[0];
                let success_block = self.builder.create_block();
                self.builder.append_block_param(success_block, I8);
                let merge_block = self.builder.create_block();
                self.builder.append_block_param(merge_block, I8);
                self.builder
                    .ins()
                    .brif(is_failure,
                        merge_block,
                        &[BlockArg::from(is_failure)],
                        success_block,
                        &[BlockArg::from(is_failure)]);
                self.builder.switch_to_block(success_block);
                self.builder.seal_block(success_block);
                {
                    $($stores)*
                }
                let is_failure = self.builder.block_params(success_block)[0];
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(is_failure)]);
                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
                let is_failure = self.builder.block_params(merge_block)[0];
                write_to_register!(
                    status_target,
                    TypedValue {
                        value: is_failure,
                        width: Width::_8,
                    },
                );
            }};
            (clrex) => {{
                let sigref = {
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(self.pointer_type));
                    self.builder.import_signature(sig)
                };
                let clrex = self
                    .builder
                    .ins()
                    .iconst(I64, crate::cpu_state::clrex as usize as u64 as i64);
                let monitor_addr = self.builder.ins().iadd_imm(
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, cpu_state.monitor) as i64,
                );
                let call = self
                    .builder
                    .ins()
                    .call_indirect(sigref, clrex, &[monitor_addr]);
                _ = self.builder.inst_results(call);
            }};
        }
        /// Perform register writeback for load/stores, after load/store is
        /// successful.
        macro_rules! write_back {
            () => {{
                if !self.writebacks.is_empty() {
                    let writebacks = std::mem::take(&mut self.writebacks);
                    for (reg, value) in writebacks {
                        let reg_view = self.reg_to_var(&reg, None, true);
                        self.def_view(&reg_view, value);
                    }
                }
            }};
        }

        macro_rules! unexpected_operand {
            ($other:expr) => {{
                let other = $other;
                panic!("unexpected lhs in {op:?}: {other:?}. Instruction: {instruction:?}")
            }};
        }
        match op {
            Op::NOP => {}
            // Special registers
            Op::MSR => {
                // [ref:can_trap]
                let mut value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                if !matches!(width, Width::_64) {
                    value = self.builder.ins().uextend(I64, value);
                }
                match instruction.operands()[0] {
                    bad64::Operand::SysReg(bad64::SysReg::DAIFSET)
                        if !matches!(&instruction.operands()[1], bad64::Operand::Imm32 { .. }) =>
                    {
                        // bad64 decodes DAIF as DAIFSet, fix it manually.
                        value = self.builder.ins().ushr_imm(value, 6);
                        sysregs::DAIF::generate_write(self, value);
                    }
                    bad64::Operand::SysReg(ref reg) => self.write_sysreg(&reg.into(), value),
                    bad64::Operand::ImplSpec { o0, o1, cm, cn, o2 } => {
                        self.write_sysreg(&SysRegEncoding { o0, o1, cm, cn, o2 }.into(), value)
                    }
                    other => unexpected_operand!(other),
                }
            }
            Op::MRS => {
                // Move System register to general-purpose register
                // [ref:can_trap]
                let target = get_destination_register!();
                let value = match instruction.operands()[1] {
                    bad64::Operand::SysReg(bad64::SysReg::DAIFSET) => {
                        // bad64 decodes DAIF as DAIFSet, fix it manually.
                        sysregs::DAIF::generate_read(self)
                    }
                    _ => self.translate_operand(&instruction.operands()[1]),
                };
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            // Memory-ops
            Op::ADRP => {
                // Form PC-relative address to 4KB page
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::ADR => {
                // Form PC-relative address
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::STLR | Op::STR => {
                // For STLR: [ref:atomics]: We don't model semantics (yet).
                let value = self.translate_operand(&instruction.operands()[0]);
                let target = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[0]);
                self.generate_write(target, value, width);
                write_back!();
            }
            Op::STLRH | Op::STURH | Op::STRH => {
                // [ref:atomics]: STLRH We don't model semantics (yet).
                let value = self.translate_operand(&instruction.operands()[0]);
                // Reduce 32-bit register to least significant halfword.
                let value = self.builder.ins().ireduce(I16, value);
                let target = self.translate_operand(&instruction.operands()[1]);
                self.generate_write(target, value, Width::_16);
                write_back!();
            }
            Op::STLRB | Op::STRB => {
                // For STLRB: [ref:atomics]: We don't model semantics (yet).
                let value = self.translate_operand(&instruction.operands()[0]);
                let target = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().ireduce(I8, value);
                self.generate_write(target, value, Width::_8);
                write_back!();
            }
            Op::STNP | Op::STP => {
                let width = self.operand_width(&instruction.operands()[0]);
                let data1 = self.translate_operand(&instruction.operands()[0]);
                let data2 = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                self.generate_write(target, data1, width);
                let target = self
                    .builder
                    .ins()
                    .iadd_imm(target, i64::from(width as i32) / 8);
                self.generate_write(target, data2, width);
                write_back!();
            }
            Op::LDXR | Op::LDAR | Op::LDR => {
                // For LDAR: [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let source_address = self.translate_operand(&instruction.operands()[1]);
                if matches!(op, Op::LDXR) {
                    monitor!(load_excl source_address);
                }
                let value = self.generate_read(source_address, width);
                write_to_register!(target, TypedValue { value, width });
                write_back!();
            }
            Op::LDNP | Op::LDP => {
                let target1 = get_destination_register!();
                let target2 = get_destination_register!(1);

                let width = target1.width;

                let source_address = self.translate_operand(&instruction.operands()[2]);

                let value = self.generate_read(source_address, width);
                write_to_register!(target1, TypedValue { value, width });
                let source_address = self
                    .builder
                    .ins()
                    .iadd_imm(source_address, i64::from(width as i32) / 8);
                let value = self.generate_read(source_address, width);
                write_to_register!(target2, TypedValue { value, width });
                write_back!();
            }
            Op::LDARH | Op::LDRH => {
                // [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, Width::_16);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_16
                    }
                );
                write_back!();
            }
            Op::LDUR => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, width);
                write_to_register!(target, TypedValue { value, width });
                write_back!();
            }
            Op::LDURB | Op::LDRB => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, Width::_8);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_8
                    },
                );
                write_back!();
            }
            Op::LDURH => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, Width::_16);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_16
                    },
                );
                write_back!();
            }
            Op::LDURSB | Op::LDRSB => {
                // Load register signed byte (register)

                // This instruction calculates an address from a base register value and an
                // offset register value, loads a byte from memory, sign-extends it, and writes
                // it to a register. For information about addressing modes
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, Width::_8);
                write_to_register!(signed target, TypedValue {
                    value,
                    width: Width::_8,
                });
                write_back!();
            }
            Op::LDURSH | Op::LDRSH => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, Width::_16);
                write_to_register!(signed target, TypedValue { value, width: Width::_16 });
                write_back!();
            }
            Op::LDURSW | Op::LDRSW => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read(source_address, Width::_32);
                write_to_register!(signed target, TypedValue {
                    value,
                    width: Width::_32
                });
                write_back!();
            }
            Op::LDPSW => {
                // Load Pair of Registers Signed Word
                // [ref:needs_unit_test]
                let target1 = get_destination_register!();
                let target2 = get_destination_register!(1);

                let source_address = self.translate_operand(&instruction.operands()[2]);

                let value = self.generate_read(source_address, Width::_32);
                write_to_register!(signed
                    target1,
                    TypedValue {
                        value,
                        width: Width::_32
                    }
                );
                let source_address = self.builder.ins().iadd_imm(source_address, 4);
                let value = self.generate_read(source_address, Width::_32);
                write_to_register!(signed
                    target2,
                    TypedValue {
                        value,
                        width: Width::_32
                    }
                );
                write_back!();
            }
            // Moves
            Op::MOV => {
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let mut width = self.operand_width(&instruction.operands()[1]);
                if width == Width::_128 {
                    width = Width::_64;
                }
                write_to_register!(target, TypedValue { value, width });
            }
            Op::MOVK => {
                let (target, target_value) = match instruction.operands()[0] {
                    bad64::Operand::Reg { ref reg, arrspec } => (
                        self.reg_to_var(reg, arrspec, true),
                        self.reg_to_value(reg, arrspec),
                    ),
                    other => unexpected_operand!(other),
                };
                let (imm_value, shift_mask): (Value, u64) = match &instruction.operands()[1] {
                    bad64::Operand::Imm32 { imm, shift } => {
                        let const_value = match imm {
                            bad64::Imm::Unsigned(imm) => {
                                self.builder.ins().iconst(I32, i64::try_from(*imm).unwrap())
                            }
                            bad64::Imm::Signed(imm) => self.builder.ins().iconst(I32, *imm),
                        };
                        match shift {
                            None => (const_value, (!u32::from(u16::MAX)).into()),
                            Some(bad64::Shift::LSL(lsl)) => {
                                let const_value =
                                    self.builder.ins().ishl_imm(const_value, i64::from(*lsl));
                                let shift_mask = !(u32::from(u16::MAX) << lsl);
                                (const_value, shift_mask.into())
                            }
                            other => unimplemented!(
                                "unimplemented shift {other:?}. Instruction: {instruction:?}"
                            ),
                        }
                    }
                    bad64::Operand::Imm64 { imm, shift } => {
                        let const_value = match imm {
                            bad64::Imm::Unsigned(imm) => {
                                self.builder.ins().iconst(I64, i64::try_from(*imm).unwrap())
                            }
                            bad64::Imm::Signed(imm) => self.builder.ins().iconst(I64, *imm),
                        };
                        match shift {
                            None => (const_value, !u64::from(u16::MAX)),
                            Some(bad64::Shift::LSL(lsl)) => {
                                let const_value =
                                    self.builder.ins().ishl_imm(const_value, i64::from(*lsl));
                                let shift_mask = !(u64::from(u16::MAX) << lsl);
                                (const_value, shift_mask)
                            }
                            other => unimplemented!(
                                "unimplemented shift {other:?}. Instruction: {instruction:?}"
                            ),
                        }
                    }
                    other => panic!("other: {:?}", other),
                };
                let width = self.operand_width(&instruction.operands()[0]);
                let mask = { self.builder.ins().iconst(width.into(), shift_mask as i64) };
                let value = self.builder.ins().bitselect(mask, target_value, imm_value);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::MOVZ => {
                let target = get_destination_register!();
                let imm_value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(
                    target,
                    TypedValue {
                        value: imm_value,
                        width,
                    },
                );
            }
            // Int-ops
            Op::ADD => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand_extended(&instruction.operands()[2], width);
                let (value, _overflow) = self.builder.ins().uadd_overflow(a, b);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::SUB => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand_extended(&instruction.operands()[2], width);
                let (value, _ignore_overflow) = self.builder.ins().usub_overflow(a, b);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::SUBS => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand_extended(&instruction.operands()[2], width);
                let negoperand2 = self.builder.ins().bnot(b);
                let one = self.builder.ins().iconst(I8, 1);
                let (result, nzcv) = self.add_with_carry(a, negoperand2, one, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::MUL => {
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().imul(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::MADD => {
                // Multiply-add
                let target = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let addend = self.translate_operand(&instruction.operands()[3]);
                let value = self.builder.ins().imul(n, m);
                let value = self.builder.ins().iadd(value, addend);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::MSUB => {
                // Multiply-subtract
                let destination = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let a = self.translate_operand(&instruction.operands()[3]);
                let b = self.builder.ins().imul(n, m);
                let (value, _ignore_overflow) = self.builder.ins().usub_overflow(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SDIV => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let dividend = self.translate_operand(&instruction.operands()[1]);
                let divisor = self.translate_operand(&instruction.operands()[2]);
                // if divisor == 0 then result = 0;
                let first_condition_value =
                    self.builder
                        .ins()
                        .icmp_imm(cranelift::prelude::IntCC::Equal, divisor, 0);

                let zero_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, width.into());

                self.builder
                    .ins()
                    .brif(first_condition_value, zero_block, &[], else_block, &[]);

                self.builder.switch_to_block(zero_block);
                self.builder.seal_block(zero_block);

                let zero = self.builder.ins().iconst(width.into(), 0);
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(zero)]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let else_return = self.builder.ins().sdiv(dividend, divisor);

                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(else_return)]);

                self.builder.switch_to_block(merge_block);

                self.builder.seal_block(merge_block);

                let phi = self.builder.block_params(merge_block)[0];

                write_to_register!(target, TypedValue { value: phi, width });
            }
            Op::UDIV => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let dividend = self.translate_operand(&instruction.operands()[1]);
                let divisor = self.translate_operand(&instruction.operands()[2]);
                // if divisor == 0 then result = 0;
                let first_condition_value =
                    self.builder
                        .ins()
                        .icmp_imm(cranelift::prelude::IntCC::Equal, divisor, 0);

                let zero_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder.append_block_param(merge_block, width.into());

                self.builder
                    .ins()
                    .brif(first_condition_value, zero_block, &[], else_block, &[]);

                self.builder.switch_to_block(zero_block);
                self.builder.seal_block(zero_block);

                let width = self.operand_width(&instruction.operands()[0]);
                let zero = self.builder.ins().iconst(width.into(), 0);
                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(zero)]);

                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let else_return = self.builder.ins().udiv(dividend, divisor);

                self.builder
                    .ins()
                    .jump(merge_block, &[BlockArg::from(else_return)]);

                self.builder.switch_to_block(merge_block);

                self.builder.seal_block(merge_block);

                let phi = self.builder.block_params(merge_block)[0];

                write_to_register!(target, TypedValue { value: phi, width });
            }
            // Branches
            Op::B => {
                // This instruction branches unconditionally to a label at a PC-relative offset,
                // with a hint that this is not a subroutine call or return.
                // constant boolean branch_conditional = FALSE;
                // BranchTo(PC64 + offset, BranchType_DIR, branch_conditional);
                let label = match instruction.operands()[0] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => unexpected_operand!(other),
                };
                let next_pc = self.builder.ins().iconst(I64, label as i64);
                return self.unconditional_jump_epilogue(next_pc);
            }
            Op::BR => {
                // This instruction branches unconditionally to an address in a register, with a
                // hint that this is not a subroutine return.
                // constant bits(64) target = X[n, 64];
                // constant boolean branch_conditional = FALSE;
                // BranchTo(target, BranchType_INDIR, branch_conditional);
                let next_pc = self.translate_operand(&instruction.operands()[0]);
                return self.unconditional_jump_epilogue(next_pc);
            }
            Op::RET => {
                let next_pc = match instruction.operands().first() {
                    Some(reg) => self.translate_operand(reg),
                    None => self.reg_to_value(&bad64::Reg::X30, None),
                };
                return self.unconditional_jump_epilogue(next_pc);
            }
            // Compares
            Op::CBNZ => {
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let label = match instruction.operands()[1] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => unexpected_operand!(other),
                };
                let is_zero_value =
                    self.builder
                        .ins()
                        .icmp_imm(cranelift::prelude::IntCC::NotEqual, operand1, 0);
                let is_zero_value = self.builder.ins().uextend(I64, is_zero_value);
                self.branch_if_non_zero(is_zero_value, label);
            }
            Op::CBZ => {
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let label = match instruction.operands()[1] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => unexpected_operand!(other),
                };
                let is_not_zero_value =
                    self.builder
                        .ins()
                        .icmp_imm(cranelift::prelude::IntCC::Equal, operand1, 0);
                let is_not_zero_value = self.builder.ins().uextend(I64, is_not_zero_value);
                self.branch_if_non_zero(is_not_zero_value, label);
            }
            // Bit-ops
            Op::BFI => {
                // Bitfield insert
                let dst = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let dst_value = self.translate_operand(&instruction.operands()[0]);
                let src_value = self.translate_operand(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let wmask = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(wmask),
                        shift: None,
                    } => self
                        .builder
                        .ins()
                        .iconst(width.into(), 2_i64.pow(wmask as u32) - 1),
                    other => unexpected_operand!(other),
                };
                let bits_to_copy = self.builder.ins().band(wmask, src_value);
                let bits_mask = self.builder.ins().rotl_imm(bits_to_copy, lsb);
                let target_mask = self.builder.ins().rotl_imm(wmask, lsb);
                let target_mask = self.builder.ins().bnot(target_mask);
                let dst_value = self.builder.ins().band(target_mask, dst_value);
                let dst_value = self.builder.ins().bor(dst_value, bits_mask);
                write_to_register!(
                    dst,
                    TypedValue {
                        value: dst_value,
                        width,
                    },
                );
            }
            Op::BFC => {
                // Bitfield clear
                // BFC <Wd>, #<lsb>, #<width>
                let destination = get_destination_register!();
                let dst_val = self.translate_operand(&instruction.operands()[0]);
                let width = self.operand_width(&instruction.operands()[0]);
                let lsb: i64 = match instruction.operands()[1] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let w: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(w),
                        shift: None,
                    } => w.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let value = self
                    .builder
                    .ins()
                    .band_imm(dst_val, !((2_i64.pow(w as u32) - 1) << lsb));
                write_to_register!(destination, TypedValue { value, width },);
            }
            Op::ORR => {
                // Bitwise OR
                // This instruction performs a bitwise (inclusive) OR of a register value and an
                // immediate value, and writes the result to the destination register.
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().bor(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::AND => {
                // Bitwise AND
                // This instruction performs a bitwise AND of a register value and an immediate
                // value, and writes the result to the destination register.
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().band(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::EOR => {
                // Bitwise XOR
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().bxor(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::EON => {
                // Bitwise XOR NOT
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let b = self.builder.ins().bnot(b);
                let value = self.builder.ins().bxor(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::LSL => {
                // Logical shift left
                // This instruction shifts a register value left by an immediate number of bits,
                // shifting in zeros, and writes the result to the destination register
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().ishl(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::LSR => {
                // Logical shift right
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().ushr(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::ASRV | Op::ASR => {
                // Arithmetic shift right (alias of SBFM)
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().sshr(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::ABS => {
                // Absolute value
                // [ref:FEAT_CSSC]
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().iabs(value);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::ADC => {
                // Add with carry
                // This instruction adds two register values and the Carry flag value, and
                // writes the result to the destination register.

                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let operand1 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.translate_operand(&instruction.operands()[2]);
                let carry_in = self.condition_holds(bad64::Condition::CS);
                let (result, _nzcv) = self.add_with_carry(operand1, operand2, carry_in, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::ADCS => {
                // Add with carry and set flags
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let operand1 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.translate_operand(&instruction.operands()[2]);
                let carry_in = self.condition_holds(bad64::Condition::CS);
                let (result, nzcv) = self.add_with_carry(operand1, operand2, carry_in, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::SBC => {
                // Subtract with carry
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let operand1 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.translate_operand(&instruction.operands()[2]);
                let operand2 = self.builder.ins().bnot(operand2);
                let carry_in = self.condition_holds(bad64::Condition::CS);
                let (result, _nzcv) = self.add_with_carry(operand1, operand2, carry_in, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::SBCS => {
                // Subtract with carry, setting flags
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let operand1 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.translate_operand(&instruction.operands()[2]);
                let operand2 = self.builder.ins().bnot(operand2);
                let carry_in = self.condition_holds(bad64::Condition::CS);
                let (result, nzcv) = self.add_with_carry(operand1, operand2, carry_in, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::NGC => {
                // Negate with carry, alias of SBC Xd, XZR, Xm
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let operand1 = self.builder.ins().iconst(width.into(), 0);
                let operand2 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.builder.ins().bnot(operand2);
                let carry_in = self.condition_holds(bad64::Condition::CS);
                let (result, _nzcv) = self.add_with_carry(operand1, operand2, carry_in, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::NGCS => {
                // Negate with carry, setting flags
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let operand1 = self.builder.ins().iconst(width.into(), 0);
                let operand2 = self.translate_operand(&instruction.operands()[1]);
                let operand2 = self.builder.ins().bnot(operand2);
                let carry_in = self.condition_holds(bad64::Condition::CS);
                let (result, nzcv) = self.add_with_carry(operand1, operand2, carry_in, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::ADDHN => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::ADDHN2 => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::ADDS => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand_extended(&instruction.operands()[2], width);
                let zero = self.builder.ins().iconst(I8, 0);
                let (result, nzcv) = self.add_with_carry(a, b, zero, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::ADDV => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::ANDS => {
                // Bitwise AND
                // This instruction performs a bitwise AND of two values and
                // updates condition flags.
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let width = self.operand_width(&instruction.operands()[1]);
                let (result, nzcv) = ands!(a, b);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::AT => todo!(),
            Op::BFMMLA
            | Op::BFMLALB
            | Op::BFMLALT
            | Op::BFCVTNT
            | Op::BFCVTN2
            | Op::BFDOT
            | Op::BFCVT => {
                // FEAT_BF16
                todo!()
            }
            Op::BFM => todo!(),
            Op::BFMOPS | Op::BFMOPA => {
                // FEAT_SME_B16B16
                todo!()
            }
            Op::BFXIL => {
                // Bitfield Extract and Insert Low (alias of BFM)
                let destination = get_destination_register!();
                let dst_val = self.translate_operand(&instruction.operands()[0]);
                let source = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let source = self.builder.ins().rotr_imm(source, lsb);
                let w: i64 = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(w),
                        shift: None,
                    } => w.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let source = self.builder.ins().band_imm(source, 2_i64.pow(w as u32) - 1);
                let dst_val = self
                    .builder
                    .ins()
                    .band_imm(dst_val, !(2_i64.pow(w as u32) - 1));
                let result = self.builder.ins().bor(source, dst_val);
                write_to_register!(
                    destination,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::BIC => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let width = self.operand_width(&instruction.operands()[1]);
                let result = self.builder.ins().band_not(a, b);
                write_to_register!(
                    destination,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::BICS => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let width = self.operand_width(&instruction.operands()[1]);
                let negb = self.builder.ins().bnot(b);
                let (result, nzcv) = ands!(a, negb);
                self.update_nzcv(nzcv);
                write_to_register!(
                    destination,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::BIF => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::BIT => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::BL => {
                let link_pc = self.builder.ins().iconst(I64, (self.address + 4) as i64);
                let link_register = self.reg_to_var(&bad64::Reg::X30, None, true);
                self.def_view(&link_register, link_pc);
                let label = match instruction.operands()[0] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => unexpected_operand!(other),
                };
                let label_value = self.builder.ins().iconst(I64, label as i64);
                return self.unconditional_jump_epilogue(label_value);
            }
            Op::BLR => {
                let next_pc = self.translate_operand(&instruction.operands()[0]);
                let link_pc = self.builder.ins().iconst(I64, (self.address + 4) as i64);
                let link_register = self.reg_to_var(&bad64::Reg::X30, None, true);
                self.def_view(&link_register, link_pc);
                return self.unconditional_jump_epilogue(next_pc);
            }
            Op::ERETAA
            | Op::ERETAB
            | Op::BLRAA
            | Op::BLRAAZ
            | Op::BLRAB
            | Op::BLRABZ
            | Op::BRAA
            | Op::BRAAZ
            | Op::BRAB
            | Op::BRABZ => {
                // FEAT_PAuth
                todo!()
            }
            Op::BRK => {
                let imm: u64 = match instruction.operands()[0] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(imm),
                        shift: None,
                    } => imm,
                    other => unexpected_operand!(other),
                };
                let imm = self.builder.ins().iconst(I16, imm as i64);

                let sigref = {
                    let mut sig = self.module.make_signature();
                    // machine: &mut crate::machine::Armv8AMachine,
                    sig.params.push(AbiParam::new(self.pointer_type));
                    // preferred_exception_return: Address,
                    sig.params.push(AbiParam::new(I64));
                    // immediate: u16,
                    sig.params.push(AbiParam::new(I16));
                    self.builder.import_signature(sig)
                };
                let func = self.builder.ins().iconst(
                    I64,
                    crate::exceptions::aarch64_software_breakpoint as usize as u64 as i64,
                );
                let pc = self.builder.ins().iconst(I64, self.address as i64);
                return self.emit_indirect_noreturn(
                    self.address,
                    sigref,
                    func,
                    &[self.machine_ptr, pc, imm],
                );
            }
            Op::BTI => {
                // NOP
            }
            Op::B_AL => b_cnd!(AL),
            Op::B_CC => b_cnd!(CC),
            Op::B_CS => b_cnd!(CS),
            Op::B_EQ => b_cnd!(EQ),
            Op::B_GE => b_cnd!(GE),
            Op::B_GT => b_cnd!(GT),
            Op::B_HI => b_cnd!(HI),
            Op::B_LE => b_cnd!(LE),
            Op::B_LS => b_cnd!(LS),
            Op::B_LT => b_cnd!(LT),
            Op::B_MI => b_cnd!(MI),
            Op::B_NE => b_cnd!(NE),
            Op::B_NV => b_cnd!(NV),
            Op::B_PL => b_cnd!(PL),
            Op::B_VC => b_cnd!(VC),
            Op::B_VS => b_cnd!(VS),
            Op::CASAB
            | Op::CASAH
            | Op::CASALB
            | Op::CASALH
            | Op::CASB
            | Op::CASH
            | Op::CASLB
            | Op::CASLH
            | Op::CASP
            | Op::CASPA
            | Op::CASPAL
            | Op::CASPL
            | Op::CASA
            | Op::CASAL
            | Op::CASL
            | Op::CAS => {
                // FEAT_LSE
                todo!()
            }
            Op::CCMN => {
                // Conditional Compare Negative; sets NZCV flags to the result of the comparison
                // of a register value and a negated value if the condition is TRUE, and an
                // immediate value otherwise
                let cnd = match instruction.operands()[3] {
                    bad64::Operand::Cond(cnd) => cnd,
                    other => panic!(
                        "expected condition argument in {op:?}: {:?}. Instruction: {instruction:?}",
                        other
                    ),
                };
                let result = self.condition_holds(cnd);
                let condition_holds_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(result, condition_holds_block, &[], else_block, &[]);
                self.builder.switch_to_block(condition_holds_block);
                self.builder.seal_block(condition_holds_block);
                // Perform regular CMP between two first operands.
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let operand2 = self.translate_operand(&instruction.operands()[1]);
                let zero = self.builder.ins().iconst(I8, 0);
                let width = self.operand_width(&instruction.operands()[0]);
                let (_result, nzcv) = self.add_with_carry(operand1, operand2, zero, width);
                // discard result, only update NZCV flags.
                self.update_nzcv(nzcv);
                self.builder.ins().jump(merge_block, &[]);
                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                // Update NZCV with value of immediate.
                {
                    let mut new_nzcv = self.translate_operand(&instruction.operands()[2]);
                    let new_nzcv_width = self.operand_width(&instruction.operands()[2]);
                    if !matches!(new_nzcv_width, Width::_64) {
                        new_nzcv = self.builder.ins().uextend(I64, new_nzcv);
                    }
                    new_nzcv = self.builder.ins().ishl_imm(new_nzcv, 28);
                    self.write_sysreg(&SysReg::NZCV, new_nzcv);
                }
                self.builder.ins().jump(merge_block, &[]);
                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
            }
            Op::CCMP => {
                // Conditional compare; set NZCV to immediate value if condition doesn't hold.
                let cnd = match instruction.operands()[3] {
                    bad64::Operand::Cond(cnd) => cnd,
                    other => panic!(
                        "expected condition argument in {op:?}: {:?}. Instruction: {instruction:?}",
                        other
                    ),
                };
                let result = self.condition_holds(cnd);
                let condition_holds_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(result, condition_holds_block, &[], else_block, &[]);
                self.builder.switch_to_block(condition_holds_block);
                self.builder.seal_block(condition_holds_block);
                // Perform regular CMP between two first operands.
                let operand1 = self.translate_operand(&instruction.operands()[0]);
                let operand2 = self.translate_operand(&instruction.operands()[1]);
                let negoperand2 = self.builder.ins().bnot(operand2);
                let one = self.builder.ins().iconst(I8, 1);
                let width = self.operand_width(&instruction.operands()[0]);
                let (_result, nzcv) = self.add_with_carry(operand1, negoperand2, one, width);
                // discard result, only update NZCV flags.
                self.update_nzcv(nzcv);
                self.builder.ins().jump(merge_block, &[]);
                self.builder.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                // Update NZCV with value of immediate.
                {
                    let mut new_nzcv = self.translate_operand(&instruction.operands()[2]);
                    let new_nzcv_width = self.operand_width(&instruction.operands()[2]);
                    if !matches!(new_nzcv_width, Width::_64) {
                        new_nzcv = self.builder.ins().uextend(I64, new_nzcv);
                    }
                    new_nzcv = self.builder.ins().ishl_imm(new_nzcv, 28);
                    self.write_sysreg(&SysReg::NZCV, new_nzcv);
                }
                self.builder.ins().jump(merge_block, &[]);
                self.builder.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
            }
            Op::CFP => {
                // FEAT_SPECRES
                todo!()
            }
            Op::CLREX => monitor!(clrex),
            Op::CLS => {
                // Count leading sign bits.
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                // [ref:cranelift_ice]: should be implemented in ISLE: inst = `v194 = cls.i32 v193`, type = `Some(types::I32)`
                // We cannot use cranelift's cls, so do some bit twiddling.
                // If we xor every bit of the input with the bit on the left, we will get as
                // many leading zeros as sign bits plus one extra zero we subtract.
                let val_shifted = self.builder.ins().sshr_imm(value, 1);
                let value = self.builder.ins().bxor(value, val_shifted);
                let value = self.builder.ins().clz(value);
                let value = self.builder.ins().iadd_imm(value, -1);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::CLZ => {
                // Count leading zeros.
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = self.builder.ins().clz(value);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::CMEQ => {
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = self.compare_by_element(a, b, width, target.element, IntCC::Equal);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::CMGT | Op::CMHI | Op::CMHS | Op::CMLE | Op::CMLT | Op::CMGE => {
                let target = get_destination_register!();
                let cond = match op {
                    Op::CMGT => IntCC::SignedGreaterThan,
                    Op::CMGE => IntCC::SignedGreaterThanOrEqual,
                    Op::CMLE => IntCC::SignedLessThanOrEqual,
                    Op::CMLT => IntCC::SignedLessThan,
                    Op::CMHI => IntCC::UnsignedGreaterThan,
                    Op::CMHS => IntCC::UnsignedGreaterThanOrEqual,
                    _ => unreachable!(),
                };
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = self.compare_by_element(a, b, width, target.element, cond);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::CMN => {
                // Compare Negative (Alias of ADDS)
                // [ref:needs_unit_test]
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.translate_operand(&instruction.operands()[0]);
                let b = self.translate_operand_extended(&instruction.operands()[1], width);
                let zero = self.builder.ins().iconst(I8, 0);
                let (_result, nzcv) = self.add_with_carry(a, b, zero, width);
                self.update_nzcv(nzcv);
            }
            Op::CMP => {
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.translate_operand(&instruction.operands()[0]);
                let b = self.translate_operand_extended(&instruction.operands()[1], width);
                let negoperand2 = self.builder.ins().bnot(b);
                let one = self.builder.ins().iconst(I8, 1);
                let (_result, nzcv) = self.add_with_carry(a, negoperand2, one, width);
                // discard result, only update NZCV flags.
                self.update_nzcv(nzcv);
            }
            Op::CMTST => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::CNT => {
                // Count bits that are one
                // [ref:FEAT_CSSC]
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = self.builder.ins().popcnt(value);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::CPY => {
                // FEAT_MOPS
                todo!()
            }
            Op::CRC32CB | Op::CRC32B => {
                let target = get_destination_register!();
                let acc = self.translate_operand(&instruction.operands()[1]);
                let byte = self.translate_operand(&instruction.operands()[2]);
                let value = crc_byte!(matches!(op, Op::CRC32CB), acc, byte);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_32
                    }
                );
            }
            Op::CRC32CH | Op::CRC32H => {
                let is_c = matches!(op, Op::CRC32CH);
                let target = get_destination_register!();
                let acc = self.translate_operand(&instruction.operands()[1]);
                let word = self.translate_operand(&instruction.operands()[2]);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let value = crc_byte!(is_c, acc, word);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_32
                    }
                );
            }
            Op::CRC32CW | Op::CRC32W => {
                let is_c = matches!(op, Op::CRC32CW);
                let target = get_destination_register!();
                let acc = self.translate_operand(&instruction.operands()[1]);
                let word = self.translate_operand(&instruction.operands()[2]);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let value = crc_byte!(is_c, acc, word);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_32
                    }
                );
            }
            Op::CRC32CX | Op::CRC32X => {
                let is_c = matches!(op, Op::CRC32CX);
                let target = get_destination_register!();
                let acc = self.translate_operand(&instruction.operands()[1]);
                let word = self.translate_operand(&instruction.operands()[2]);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let acc = crc_byte!(is_c, acc, word);
                let word = self.builder.ins().ushr_imm(word, 8);
                let value = crc_byte!(is_c, acc, word);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_32
                    }
                );
            }
            Op::CSDB => {
                // Consumption of speculative data barrier
            }
            Op::CSEL => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let true_value = self.translate_operand(&instruction.operands()[1]);
                let false_value = self.translate_operand(&instruction.operands()[2]);
                let cond = match instruction.operands()[3] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                let result = self.condition_holds(cond);
                let result = self.builder.ins().uextend(width.into(), result);
                let phi_block = self.builder.create_block();

                self.builder.append_block_param(phi_block, width.into());
                self.builder.ins().brif(
                    result,
                    phi_block,
                    &[BlockArg::from(true_value)],
                    phi_block,
                    &[BlockArg::from(false_value)],
                );
                self.builder.switch_to_block(phi_block);
                self.builder.seal_block(phi_block);

                let phi = self.builder.block_params(phi_block)[0];
                write_to_register!(target, TypedValue { value: phi, width });
            }
            Op::CSET => {
                // Conditional set: an alias of CSINC.
                // This instruction sets the destination register to 1 if the condition is TRUE,
                // and otherwise sets it to 0.

                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let zero = self.builder.ins().iconst(width.into(), 0);
                let cond = match instruction.operands()[1] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { inc Rd = target, Rn = zero, Rm = zero, cond = condition_holds!(invert cond), width = width };
            }
            Op::CSINC => {
                // Conditional select increment

                // This instruction returns, in the destination register, the value of the first
                // source register if the condition is TRUE, and otherwise
                // returns the value of the second source register incremented
                // by 1.

                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let true_value = self.translate_operand(&instruction.operands()[1]);
                let false_value = self.translate_operand(&instruction.operands()[2]);
                let cond = match instruction.operands()[3] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { inc Rd = target, Rn = true_value, Rm = false_value, cond = condition_holds!(cond), width = width };
            }
            Op::CINC => {
                // Conditional increment: an alias of CSINC.
                // This instruction returns, in the destination register, the value of the
                // source register incremented by 1 if the condition is TRUE,
                // and otherwise returns the value of the source register.

                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let value = self.translate_operand(&instruction.operands()[1]);
                let cond = match instruction.operands()[2] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { inc Rd = target, Rn = value, Rm = value, cond = condition_holds!(invert cond), width = width };
            }
            Op::CSINV => {
                // Conditional select invert

                // This instruction returns, in the destination register, the value of the first
                // source register if the condition is TRUE, and otherwise
                // returns the bitwise inversion value of the second source
                // register.
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let true_value = self.translate_operand(&instruction.operands()[1]);
                let false_value = self.translate_operand(&instruction.operands()[2]);
                let cond = match instruction.operands()[3] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { inv Rd = target, Rn = true_value, Rm = false_value, cond = condition_holds!(cond), width = width };
            }
            Op::CINV => {
                // Conditional invert: an alias of CSINV.
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let value = self.translate_operand(&instruction.operands()[1]);
                let cond = match instruction.operands()[2] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { inv Rd = target, Rn = value, Rm = value, cond = condition_holds!(invert cond), width = width };
            }
            Op::CSETM => {
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let zero = self.builder.ins().iconst(width.into(), 0);
                let cond = match instruction.operands()[1] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { inv Rd = target, Rn = zero, Rm = zero, cond = condition_holds!(invert cond), width = width };
            }
            Op::CSNEG => {
                // Conditional select negation
                // This instruction returns, in the destination register, the value of the first
                // source register if the condition is TRUE, and otherwise
                // returns the negated value of the second source register.
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let true_value = self.translate_operand(&instruction.operands()[1]);
                let false_value = self.translate_operand(&instruction.operands()[2]);
                let cond = match instruction.operands()[3] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { neg Rd = target, Rn = true_value, Rm = false_value, cond = condition_holds!(cond), width = width };
            }
            Op::CNEG => {
                // Conditional negate
                // This instruction returns, in the destination register, the negated value of
                // the source register if the condition is TRUE, and otherwise
                // returns the value of the source register. This is an alias of
                // CSNEG. [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let value = self.translate_operand(&instruction.operands()[1]);
                let cond = match instruction.operands()[2] {
                    bad64::Operand::Cond(cond) => cond,
                    other => unexpected_operand!(other),
                };
                cs! { neg Rd = target, Rn = value, Rm = value, cond = condition_holds!(invert cond), width = width };
            }
            Op::DC => {
                // Data Cache operation
                match instruction.operands()[0] {
                    bad64::Operand::Name(n) if n.starts_with(b"zva\0") => {
                        let vaddress = self.translate_operand(&instruction.operands()[1]);
                        self.store_pc(None);
                        let preferred_exception_return =
                            self.builder.ins().iconst(I64, self.address as i64);
                        let sigref = {
                            let mut sig = self.module.make_signature();
                            sig.params.push(AbiParam::new(self.pointer_type));
                            sig.params.push(AbiParam::new(I64));
                            sig.params.push(AbiParam::new(I64));
                            sig.returns.push(AbiParam::new(I8));
                            self.builder.import_signature(sig)
                        };
                        let mem_zero = self
                            .builder
                            .ins()
                            .iconst(I64, crate::memory::mmu::mem_zero as usize as u64 as i64);
                        let call = self.builder.ins().call_indirect(
                            sigref,
                            mem_zero,
                            &[self.machine_ptr, vaddress, preferred_exception_return],
                        );
                        let success = self.builder.inst_results(call)[0];
                        let failure_block = self.builder.create_block();
                        let merge_block = self.builder.create_block();
                        self.builder
                            .ins()
                            .brif(success, merge_block, &[], failure_block, &[]);
                        self.builder.switch_to_block(failure_block);
                        self.builder.seal_block(failure_block);
                        self.store_pc(None);
                        self.direct_exit(BlockExit::Exception);
                        self.builder.switch_to_block(merge_block);
                        self.builder.seal_block(merge_block);
                    }
                    _ => {}
                }
            }
            Op::DRPS => todo!(),
            Op::DCPS1 => todo!(),
            Op::DCPS2 => todo!(),
            Op::DCPS3 => todo!(),
            Op::DGH => {
                // FEAT_DGH
                todo!()
            }
            Op::DMB => {
                // Data Memory Barrier
            }
            Op::DSB => {
                // Data synchronization barrier
            }
            Op::DUP => {
                // Duplicate general-purpose register to vector
                let target = get_destination_register!();
                let target_element_size = Width::from(target.element.unwrap());
                let elem = {
                    let mut elem = self.translate_operand(&instruction.operands()[1]);
                    let width = self.operand_width(&instruction.operands()[1]);
                    if width > target_element_size {
                        elem = self.builder.ins().ireduce(target_element_size.into(), elem);
                    } else if width < target_element_size {
                        elem = self.builder.ins().uextend(target_element_size.into(), elem);
                    }
                    elem
                };
                let elements = i64::from(i32::from(target.width) / i32::from(target_element_size));

                let mut value = self.simd_iconst(target.width, 0);
                for i in 0..elements {
                    value = self.set_elem(value, i, target_element_size, elem);
                }
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: target.width,
                    }
                );
            }
            Op::DUPM => todo!(),
            Op::UMOV => {
                let target = get_destination_register!();
                let (value, arrspec) = match instruction.operands()[1] {
                    bad64::Operand::Reg { ref reg, arrspec } => {
                        (self.reg_to_value(reg, arrspec), arrspec.unwrap())
                    }
                    other => unexpected_operand!(other),
                };
                let width = arrspec.into();
                write_to_register!(target, TypedValue { value, width });
            }
            Op::DVP => todo!(),
            Op::EORS => todo!(),
            Op::EORV => todo!(),
            Op::ERET => {
                let sigref = {
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(self.pointer_type));
                    sig.params.push(AbiParam::new(I64));
                    self.builder.import_signature(sig)
                };
                let func = self.builder.ins().iconst(
                    I64,
                    crate::exceptions::aarch64_exception_return as usize as u64 as i64,
                );
                let pc = self.builder.ins().iconst(I64, self.address as i64);
                return self.emit_indirect_noreturn(
                    self.address,
                    sigref,
                    func,
                    &[self.machine_ptr, pc],
                );
            }
            Op::ESB => {
                // FEAT_RAS
                todo!()
            }
            Op::EXT => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::EXTR => {
                // Extract register extracts a register from a pair of registers.
                let target = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let lsb: i64 = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let width = self.operand_width(&instruction.operands()[1]);
                let n = if lsb == 0 {
                    self.builder.ins().iconst(width.into(), 0)
                } else {
                    self.builder.ins().ishl_imm(n, width as i64 - lsb)
                };
                let m = self.builder.ins().ushr_imm(m, lsb);
                let value = self.builder.ins().bor(n, m);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::FABD => todo!(),
            Op::FABS => todo!(),
            Op::FACGE => todo!(),
            Op::FACGT => todo!(),
            Op::FACLE => todo!(),
            Op::FACLT => todo!(),
            Op::FADD => todo!(),
            Op::FADDA => todo!(),
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
            Op::FCVTMS => todo!(),
            Op::FCVTMU => todo!(),
            Op::FCVTN2 => todo!(),
            Op::FCVTNS => todo!(),
            Op::FCVTNU => todo!(),
            Op::FCVTPS => todo!(),
            Op::FCVTPU => todo!(),
            Op::FCVTXN => todo!(),
            Op::FCVTXN2 => todo!(),
            Op::FCVTZS => todo!(),
            Op::FCVTZU => todo!(),
            Op::FDIV => todo!(),
            Op::FDIVR => todo!(),
            Op::FDUP => todo!(),
            Op::FEXPA => todo!(),
            Op::FJCVTZS => todo!(),
            Op::FMAD => todo!(),
            Op::FMADD => todo!(),
            Op::FMAX => todo!(),
            Op::FMAXNM => todo!(),
            Op::FMAXNMV => todo!(),
            Op::FMAXV => todo!(),
            Op::FMIN => todo!(),
            Op::FMINNM => todo!(),
            Op::FMINNMV => todo!(),
            Op::FMINV => todo!(),
            Op::FMLA => todo!(),
            Op::FMLAL => todo!(),
            Op::FMLAL2 => todo!(),
            Op::FMLS => todo!(),
            Op::FMLSL => todo!(),
            Op::FMLSL2 => todo!(),
            Op::FMMLA => todo!(),
            Op::FMOPA => todo!(),
            Op::FMOPS => todo!(),
            Op::FMOV => {
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
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
            Op::HINT => todo!(),
            Op::HLT => {
                return ControlFlow::Break(None);
            }
            Op::HVC => {
                let imm: u64 = match instruction.operands()[0] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(imm),
                        shift: None,
                    } => imm,
                    other => unexpected_operand!(other),
                };
                let imm = self.builder.ins().iconst(I16, imm as i64);

                let sigref = {
                    let mut sig = self.module.make_signature();
                    // machine: &mut crate::machine::Armv8AMachine,
                    sig.params.push(AbiParam::new(self.pointer_type));
                    // preferred_exception_return: Address,
                    sig.params.push(AbiParam::new(I64));
                    // immediate: u16,
                    sig.params.push(AbiParam::new(I16));
                    self.builder.import_signature(sig)
                };
                let func = self.builder.ins().iconst(
                    I64,
                    crate::exceptions::aarch64_call_hypervisor as usize as u64 as i64,
                );
                let next_pc = self.builder.ins().iconst(I64, self.address as i64 + 4);
                return self.emit_indirect_noreturn(
                    self.address,
                    sigref,
                    func,
                    &[self.machine_ptr, next_pc, imm],
                );
            }
            Op::SVC => {
                let imm: u64 = match instruction.operands()[0] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(imm),
                        shift: None,
                    } => imm,
                    other => unexpected_operand!(other),
                };
                let imm = self.builder.ins().iconst(I16, imm as i64);

                let sigref = {
                    let mut sig = self.module.make_signature();
                    // machine: &mut crate::machine::Armv8AMachine,
                    sig.params.push(AbiParam::new(self.pointer_type));
                    // preferred_exception_return: Address,
                    sig.params.push(AbiParam::new(I64));
                    // immediate: u16,
                    sig.params.push(AbiParam::new(I16));
                    self.builder.import_signature(sig)
                };
                let func = self.builder.ins().iconst(
                    I64,
                    crate::exceptions::aarch64_call_supervisor as usize as u64 as i64,
                );
                let next_pc = self.builder.ins().iconst(I64, self.address as i64 + 4);
                return self.emit_indirect_noreturn(
                    self.address,
                    sigref,
                    func,
                    &[self.machine_ptr, next_pc, imm],
                );
            }
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
            Op::ISB => {
                // Instruction synchronization barrier
                return self.r#yield(ExitRequestID::Yield);
            }
            Op::LASTA => todo!(),
            Op::LASTB => todo!(),
            Op::LD1 => {
                let (targets, arrspec) = match instruction.operands()[0] {
                    bad64::Operand::MultiReg { regs, arrspec } => (regs, arrspec.unwrap()),
                    other => unexpected_operand!(other),
                };
                let element_address = self.translate_operand(&instruction.operands()[1]);
                let element_width = arrspec.into();
                for (i, v) in targets.into_iter().enumerate() {
                    let Some(reg) = v else {
                        break;
                    };
                    let target = self.simd_reg_to_var(&reg, Some(arrspec), true);
                    let value = self.simd_reg_view_to_value(target, Some(arrspec));
                    let element_address = self.builder.ins().iadd_imm(
                        element_address,
                        i as i64 * i64::from(element_width as i32 / 8),
                    );
                    let element_value = self.generate_read(element_address, element_width);
                    let value = self.set_elem(value, i as i64, element_width, element_value);
                    write_to_register!(
                        target,
                        TypedValue {
                            value,
                            width: target.width,
                        }
                    );
                }
                write_back!();
            }
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
            Op::LDAXR => {
                // [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let source_address = self.translate_operand(&instruction.operands()[1]);
                monitor!(load_excl source_address);
                let value = self.generate_read(source_address, width);
                write_to_register!(target, TypedValue { value, width });
                write_back!();
            }
            Op::LDARB | Op::LDAXRB => {
                // [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                if matches!(op, Op::LDAXRB) {
                    monitor!(load_excl source_address);
                }
                let value = self.generate_read(source_address, Width::_8);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_8
                    },
                );
                write_back!();
            }
            Op::LDAXRH => {
                // [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                monitor!(load_excl source_address);
                let value = self.generate_read(source_address, Width::_16);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_16
                    },
                );
                write_back!();
            }
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
            Op::LDNT1B => todo!(),
            Op::LDNT1D => todo!(),
            Op::LDNT1H => todo!(),
            Op::LDNT1SB => todo!(),
            Op::LDNT1SH => todo!(),
            Op::LDNT1SW => todo!(),
            Op::LDNT1W => todo!(),
            Op::LDRAA => todo!(),
            Op::LDRAB => todo!(),
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
            Op::LDTR => {
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read_unprivileged(source_address, width);
                write_to_register!(target, TypedValue { value, width });
                write_back!();
            }
            Op::LDTRB => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read_unprivileged(source_address, Width::_8);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_8
                    },
                );
                write_back!();
            }
            Op::LDTRH => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read_unprivileged(source_address, Width::_16);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_16
                    }
                );
                write_back!();
            }
            Op::LDTRSB => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read_unprivileged(source_address, Width::_8);
                write_to_register!(signed target, TypedValue {
                    value,
                    width: Width::_8,
                });
                write_back!();
            }
            Op::LDTRSH => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read_unprivileged(source_address, Width::_16);
                write_to_register!(signed target, TypedValue { value, width: Width::_16 });
                write_back!();
            }
            Op::LDTRSW => {
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                let value = self.generate_read_unprivileged(source_address, Width::_32);
                write_to_register!(signed target, TypedValue {
                    value,
                    width: Width::_32
                });
                write_back!();
            }
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
            Op::LDAXP | Op::LDXP => {
                // LDAXP: [ref:atomics]: We don't model semantics (yet).
                let target1 = get_destination_register!();
                let target2 = get_destination_register!(1);

                let width = target1.width;

                let source_address = self.translate_operand(&instruction.operands()[2]);
                monitor!(load_excl source_address);

                let value = self.generate_read(source_address, width);
                write_to_register!(target1, TypedValue { value, width });
                let source_address = self
                    .builder
                    .ins()
                    .iadd_imm(source_address, i64::from(width as i32) / 8);
                let value = self.generate_read(source_address, width);
                write_to_register!(target2, TypedValue { value, width });
                write_back!();
            }
            Op::LDXRB => {
                // [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                monitor!(load_excl source_address);
                let value = self.generate_read(source_address, Width::_8);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_8
                    },
                );
                write_back!();
            }
            Op::LDXRH => {
                // [ref:atomics]: We don't model semantics (yet).
                let target = get_destination_register!();
                let source_address = self.translate_operand(&instruction.operands()[1]);
                monitor!(load_excl source_address);
                let value = self.generate_read(source_address, Width::_16);
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: Width::_16
                    },
                );
                write_back!();
            }
            Op::LSLR => todo!(),
            Op::LSLV => todo!(),
            Op::LSRR => todo!(),
            Op::LSRV => todo!(),
            Op::MAD => todo!(),
            Op::MNEG => {
                // Alias of MSUB
                let destination = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().imul(n, m);
                let value = self.builder.ins().ineg(value);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::MOVA => todo!(),
            Op::MOVI => {
                // Move Immediate (vector). This instruction places an immediate constant into
                // every vector element of the destination SIMD&FP register.
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                // [ref:cranelift_ice]: Cranelift ICEs with "should be implemented in ISLE:" error when
                // using 64-bit vector types, so use 128-bit types and reduce them to I64 type
                // manually.
                let (reduce, vector_type, value) = match target.element {
                    Some(ArrSpec::TwoDoubles(None)) => (false, I64X2, value),
                    Some(ArrSpec::EightBytes(None)) => {
                        (true, I8X16, self.builder.ins().ireduce(I8, value))
                    }
                    Some(ArrSpec::SixteenBytes(None)) => {
                        (false, I8X16, self.builder.ins().ireduce(I8, value))
                    }
                    Some(ArrSpec::FourHalves(None)) => {
                        (true, I16X8, self.builder.ins().ireduce(I16, value))
                    }
                    Some(ArrSpec::EightHalves(None)) => {
                        (false, I16X8, self.builder.ins().ireduce(I16, value))
                    }
                    Some(ArrSpec::TwoSingles(None)) => (true, I32X4, value),
                    Some(ArrSpec::FourSingles(None)) => (false, I32X4, value),
                    other => unimplemented!("{other:?}"),
                };
                let value = self.builder.ins().splat(vector_type, value);
                let value = self
                    .builder
                    .ins()
                    .bitcast(I128, MEMFLAG_LITTLE_ENDIAN, value);
                let (value, width) = if reduce {
                    let value = self.builder.ins().ireduce(I64, value);
                    (value, Width::_64)
                } else {
                    (value, Width::_128)
                };
                write_to_register!(target, TypedValue { value, width });
            }
            Op::MOVN => {
                let target = get_destination_register!();
                let imm_value = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().bnot(imm_value);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width },);
            }
            Op::MOVPRFX => todo!(),
            Op::MOVS => todo!(),
            Op::MSB => todo!(),
            Op::MVN => {
                // FEAT_AdvSIMD
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let mut value = self.builder.ins().bnot(value);
                let width = self.operand_width(&instruction.operands()[0]);
                if width == Width::_32 {
                    value = self.builder.ins().band_imm(value, i64::from(u32::MAX));
                }
                write_to_register!(target, TypedValue { value, width });
            }
            Op::MVNI => {
                // FEAT_AdvSIMD
                // [ref:needs_unit_test]
                // Move Negated Immediate (vector). This instruction places an inverted
                // immediate constant into every vector element of the
                // destination SIMD&FP register.
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().bnot(value);
                // [ref:cranelift_ice]: Cranelift ICEs with "should be implemented in ISLE:" error when
                // using 64-bit vector types, so use 128-bit types and reduce them to I64 type
                // manually.
                let (reduce, vector_type, value) = match target.element {
                    Some(ArrSpec::TwoDoubles(None)) => (false, I64X2, value),
                    Some(ArrSpec::EightBytes(None)) => {
                        (true, I8X16, self.builder.ins().ireduce(I8, value))
                    }
                    Some(ArrSpec::SixteenBytes(None)) => {
                        (false, I8X16, self.builder.ins().ireduce(I8, value))
                    }
                    Some(ArrSpec::FourHalves(None)) => {
                        (true, I16X8, self.builder.ins().ireduce(I16, value))
                    }
                    Some(ArrSpec::EightHalves(None)) => {
                        (false, I16X8, self.builder.ins().ireduce(I16, value))
                    }
                    Some(ArrSpec::TwoSingles(None)) => (true, I32X4, value),
                    Some(ArrSpec::FourSingles(None)) => (false, I32X4, value),
                    other => unimplemented!("{other:?}"),
                };
                let value = self.builder.ins().splat(vector_type, value);
                let value = self
                    .builder
                    .ins()
                    .bitcast(I128, MEMFLAG_LITTLE_ENDIAN, value);
                let (value, width) = if reduce {
                    let value = self.builder.ins().ireduce(I64, value);
                    (value, Width::_64)
                } else {
                    (value, Width::_128)
                };
                write_to_register!(target, TypedValue { value, width });
            }
            Op::NAND => todo!(),
            Op::NANDS => todo!(),
            Op::NEG => {
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let mut value = self.builder.ins().ineg(value);
                let width = self.operand_width(&instruction.operands()[0]);
                if width == Width::_32 {
                    value = self.builder.ins().band_imm(value, i64::from(u32::MAX));
                }
                write_to_register!(target, TypedValue { value, width });
            }
            Op::NEGS => {
                // Negate, setting flags (alias of SUBS)
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[0]);
                let a = self.builder.ins().iconst(width.into(), 0);
                let b = self.translate_operand_extended(&instruction.operands()[1], width);
                let negoperand2 = self.builder.ins().bnot(b);
                let one = self.builder.ins().iconst(I8, 1);
                let (result, nzcv) = self.add_with_carry(a, negoperand2, one, width);
                write_to_register!(
                    target,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
                self.update_nzcv(nzcv);
            }
            Op::NOR => todo!(),
            Op::NORS => todo!(),
            Op::NOT => todo!(),
            Op::NOTS => todo!(),
            Op::ORN => {
                // Bitwise OR NOT
                // [ref:needs_unit_test]
                let target = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let b = self.builder.ins().bnot(b);
                let value = self.builder.ins().bor(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::ORNS => todo!(),
            Op::ORRS => todo!(),
            Op::ORV => todo!(),
            Op::AUTDA
            | Op::AUTDB
            | Op::AUTDZA
            | Op::AUTDZB
            | Op::AUTIA
            | Op::AUTIA1716
            | Op::AUTIAZ
            | Op::AUTIB
            | Op::AUTIB1716
            | Op::AUTIBSP
            | Op::AUTIBZ
            | Op::AUTIZA
            | Op::AUTIZB
            | Op::PACIAZ
            | Op::PACIB
            | Op::PACIB1716
            | Op::PACIBSP
            | Op::PACIBZ
            | Op::PACIZA
            | Op::PACIZB
            | Op::PACDA
            | Op::PACDB
            | Op::PACDZA
            | Op::PACDZB
            | Op::PACGA
            | Op::PACIA
            | Op::PACIA1716
            | Op::XPACD
            | Op::XPACI
            | Op::XPACLRI
            | Op::AUTIASP
            | Op::PACIASP => {
                // [ref:pointer_auth]
                // NOP
            }
            Op::PFALSE => todo!(),
            Op::PFIRST => todo!(),
            Op::PMULL => todo!(),
            Op::PMULL2 => todo!(),
            Op::PNEXT => todo!(),
            Op::CPP | Op::PRFB | Op::PRFD | Op::PRFH | Op::PRFW | Op::PRFUM | Op::PRFM => {
                // Prefetch Memory
                // NOP
            }
            Op::PSB => todo!(),
            Op::PSSBB => todo!(),
            Op::PTEST => todo!(),
            Op::PTRUES => todo!(),
            Op::PUNPKHI => todo!(),
            Op::PUNPKLO => todo!(),
            Op::RADDHN => todo!(),
            Op::RADDHN2 => todo!(),
            Op::RBIT => {
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().bitrev(value);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::RDFFR => todo!(),
            Op::RDFFRS => todo!(),
            Op::RDVL => todo!(),
            Op::RETAA => todo!(),
            Op::RETAB => todo!(),
            Op::REV | Op::REV64 => {
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = self.builder.ins().bswap(value);
                write_to_register!(target, TypedValue { value, width });
            }
            Op::REV16 => {
                // Reverse bytes in 16-bit words
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);

                match width {
                    Width::_32 => {
                        let h_1 = self.builder.ins().ireduce(I16, value);
                        let h_1 = self.builder.ins().bswap(h_1);
                        let h_1 = self.builder.ins().uextend(I32, h_1);

                        let h_2 = self.builder.ins().ushr_imm(value, 16);
                        let h_2 = self.builder.ins().ireduce(I16, h_2);
                        let h_2 = self.builder.ins().bswap(h_2);
                        let h_2 = self.builder.ins().uextend(I32, h_2);
                        let h_2 = self.builder.ins().ishl_imm(h_2, 16);

                        let value = self.builder.ins().bor(h_1, h_2);

                        write_to_register!(target, TypedValue { value, width });
                    }
                    Width::_64 => {
                        let h_1 = self.builder.ins().ireduce(I16, value);
                        let h_1 = self.builder.ins().bswap(h_1);
                        let h_1 = self.builder.ins().uextend(I64, h_1);

                        let h_2 = self.builder.ins().ushr_imm(value, 16);
                        let h_2 = self.builder.ins().ireduce(I16, h_2);
                        let h_2 = self.builder.ins().bswap(h_2);
                        let h_2 = self.builder.ins().uextend(I64, h_2);
                        let h_2 = self.builder.ins().ishl_imm(h_2, 16);

                        let h_3 = self.builder.ins().ushr_imm(value, 32);
                        let h_3 = self.builder.ins().ireduce(I16, h_3);
                        let h_3 = self.builder.ins().bswap(h_3);
                        let h_3 = self.builder.ins().uextend(I64, h_3);
                        let h_3 = self.builder.ins().ishl_imm(h_3, 32);

                        let h_4 = self.builder.ins().ushr_imm(value, 48);
                        let h_4 = self.builder.ins().ireduce(I16, h_4);
                        let h_4 = self.builder.ins().bswap(h_4);
                        let h_4 = self.builder.ins().uextend(I64, h_4);
                        let h_4 = self.builder.ins().ishl_imm(h_4, 48);

                        let value = self.builder.ins().bor(h_1, h_2);
                        let value = self.builder.ins().bor(value, h_3);
                        let value = self.builder.ins().bor(value, h_4);

                        write_to_register!(target, TypedValue { value, width });
                    }
                    other => unimplemented!("{other:?}"),
                }
            }
            Op::REV32 => {
                // Reverse bytes in 32-bit words reverses the byte order in each 32-bit word of
                // a register.
                let target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[1]);

                macro_rules! reverse_word {
                    ($word_value:expr, lsb = $lsb:expr) => {{
                        let word = if $lsb > 0 {
                            self.builder.ins().ushr_imm($word_value, $lsb)
                        } else {
                            $word_value
                        };
                        let word = self.builder.ins().ireduce(I32, word);
                        let word = self.builder.ins().bswap(word);
                        let word = self.builder.ins().uextend(I64, word);
                        if $lsb > 0 {
                            self.builder.ins().ishl_imm(word, $lsb)
                        } else {
                            word
                        }
                    }};
                }
                let value = if matches!(width, Width::_128) {
                    let w_1 = self.builder.ins().band_imm(value, i64::from(u32::MAX));
                    let w_1 = self.builder.ins().ireduce(I64, w_1);
                    let w_2 = self.builder.ins().ireduce(I64, value);
                    let hdw = self.builder.ins().ushr_imm(value, 64);
                    let w_3 = self.builder.ins().band_imm(hdw, i64::from(u32::MAX));
                    let w_3 = self.builder.ins().ireduce(I64, w_3);
                    let w_4 = self.builder.ins().ireduce(I64, hdw);
                    let w_1 = reverse_word!(w_1, lsb = 0);
                    let w_2 = reverse_word!(w_2, lsb = 32);
                    let w_3 = reverse_word!(w_3, lsb = 0);
                    let w_4 = reverse_word!(w_4, lsb = 32);
                    let low = self.builder.ins().bor(w_1, w_2);
                    let high = self.builder.ins().bor(w_3, w_4);
                    self.builder.ins().iconcat(low, high)
                } else {
                    let a = self.builder.ins().band_imm(value, i64::from(u32::MAX));
                    let a = self.builder.ins().ireduce(I32, a);
                    let a = self.builder.ins().bswap(a);
                    let a = self.builder.ins().uextend(I64, a);
                    let b = self.builder.ins().ushr_imm(value, 32);
                    let b = self.builder.ins().ireduce(I32, b);
                    let b = self.builder.ins().bswap(b);
                    let b = self.builder.ins().uextend(I64, b);
                    let b = self.builder.ins().ishl_imm(b, 32);
                    self.builder.ins().bor(a, b)
                };
                write_to_register!(target, TypedValue { value, width });
            }
            Op::REVB => todo!(),
            Op::REVH => todo!(),
            Op::REVW => todo!(),
            Op::RMIF => todo!(),
            Op::ROR => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let rotr = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().rotr(value, rotr);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::RORV => todo!(),
            Op::RSHRN => todo!(),
            Op::RSHRN2 => todo!(),
            Op::RSUBHN => todo!(),
            Op::RSUBHN2 => todo!(),
            Op::SABAL => todo!(),
            Op::SABAL2 => todo!(),
            Op::SABD => todo!(),
            Op::SABDL => todo!(),
            Op::SABDL2 => todo!(),
            Op::SADDL => todo!(),
            Op::SADDL2 => todo!(),
            Op::SADDLP => todo!(),
            Op::SADDLV => todo!(),
            Op::SADDV => todo!(),
            Op::SADDW => todo!(),
            Op::SADDW2 => todo!(),
            Op::SB => todo!(),
            Op::SBFIZ => {
                let destination = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb as i64,
                    other => unexpected_operand!(other),
                };
                let wmask: i64 = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(wmask),
                        shift: None,
                    } => wmask as i64,
                    other => unexpected_operand!(other),
                };
                let value = self
                    .builder
                    .ins()
                    .band_imm(value, 2_i64.pow(wmask as u32) - 1);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = sign_extend_bitfield!(value, wmask, width);
                let value = self.builder.ins().ishl_imm(value, lsb);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SBFM => todo!(),
            Op::SXTW => {
                // Alias of SBFM <Xd>, <Xn>, #0, #31
                let destination = get_destination_register!();
                let w = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().sextend(destination.width.into(), w);
                write_to_register!(
                    destination,
                    TypedValue {
                        value,
                        width: destination.width
                    }
                );
            }
            Op::SXTB => {
                // Sign Extend Byte Alias of SBFM <Rd>, <Rn>, #0, #7
                let destination = get_destination_register!();
                let w = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().ireduce(I8, w);
                let value = self.builder.ins().sextend(destination.width.into(), value);
                write_to_register!(
                    destination,
                    TypedValue {
                        value,
                        width: destination.width
                    }
                );
            }
            Op::SXTH => {
                // Sign Extend Halfword Alias of SBFM <Rd>, <Rn>, #0, #15
                let destination = get_destination_register!();
                let w = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().ireduce(I16, w);
                let value = self.builder.ins().sextend(destination.width.into(), value);
                write_to_register!(
                    destination,
                    TypedValue {
                        value,
                        width: destination.width
                    }
                );
            }
            Op::SBFX => {
                let destination = get_destination_register!();
                let source = self.translate_operand(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let wmask = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(wmask),
                        shift: None,
                    } => wmask,
                    other => unexpected_operand!(other),
                };
                let value = self
                    .builder
                    .ins()
                    .band_imm(source, (2_i64.pow(wmask as u32) - 1) << lsb);
                let value = self.builder.ins().ushr_imm(value, lsb);
                let width = self.operand_width(&instruction.operands()[1]);
                let value = sign_extend_bitfield!(value, wmask, width);
                write_to_register!(destination, TypedValue { value, width },);
            }
            Op::SCVTF => todo!(),
            Op::SDIVR => todo!(),
            Op::SDOT => todo!(),
            Op::SEL => todo!(),
            Op::SETF16 => todo!(),
            Op::SETF8 => todo!(),
            Op::SETFFR => todo!(),
            Op::SEV | Op::SEVL => {
                let true_val = self.builder.ins().iconst(I8, i64::from(true));
                self.builder.ins().store(
                    TRUSTED_MEMFLAGS,
                    true_val,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, cpu_state.monitor.event_register) as i32,
                );
            }
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
            Op::SHL => todo!(),
            Op::SHLL => todo!(),
            Op::SHLL2 => todo!(),
            Op::SHRN => {
                let target = get_destination_register!();
                let target_element_size = Width::from(target.element.unwrap());
                let (source_reg, source_element_size) = match instruction.operands()[1] {
                    bad64::Operand::Reg { reg, arrspec } => (reg, Width::from(arrspec.unwrap())),
                    other => unexpected_operand!(other),
                };
                let source_value = self.simd_reg_to_value(&source_reg, None);
                let elements = i64::from(i32::from(target.width) / i32::from(target_element_size));
                let shift = self.translate_operand(&instruction.operands()[2]);

                let mut value = self.simd_iconst(target.width, 0);
                for i in 0..elements {
                    let elem = self.get_elem(source_value, i, source_element_size);
                    let elem = self.builder.ins().ireduce(target_element_size.into(), elem);
                    let elem = self.builder.ins().ushr(elem, shift);
                    value = self.set_elem(value, i, target_element_size, elem);
                }
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: target.width,
                    }
                );
            }
            Op::UMAXP => {
                let target = get_destination_register!();
                let (a_reg, element_size) = match instruction.operands()[1] {
                    bad64::Operand::Reg { reg, arrspec } => (reg, Width::from(arrspec.unwrap())),
                    other => unexpected_operand!(other),
                };
                let a_value = self.simd_reg_to_value(&a_reg, None);
                let b_reg = match instruction.operands()[2] {
                    bad64::Operand::Reg { reg, arrspec: _ } => reg,
                    other => unexpected_operand!(other),
                };
                let b_value = self.simd_reg_to_value(&b_reg, None);
                let elements = i64::from(i32::from(target.width) / i32::from(element_size));

                let mut value = self.simd_iconst(target.width, 0);
                for i in 0..elements {
                    let a_idx = 2 * i;
                    let b_idx = 2 * i + 1;
                    let a = if a_idx < elements {
                        self.get_elem(a_value, a_idx, element_size)
                    } else {
                        self.get_elem(b_value, a_idx - elements, element_size)
                    };
                    let b = if b_idx < elements {
                        self.get_elem(a_value, b_idx, element_size)
                    } else {
                        self.get_elem(b_value, b_idx - elements, element_size)
                    };
                    let max = self.builder.ins().umax(a, b);
                    value = self.set_elem(value, i, element_size, max);
                }
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: target.width,
                    }
                );
            }
            Op::SHRN2 => todo!(),
            Op::SM3PARTW1 => todo!(),
            Op::SM3PARTW2 => todo!(),
            Op::SM3SS1 => todo!(),
            Op::SM3TT1A => todo!(),
            Op::SM3TT1B => todo!(),
            Op::SM3TT2A => todo!(),
            Op::SM3TT2B => todo!(),
            Op::SMADDL => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let c = self.translate_operand(&instruction.operands()[3]);
                let a = self.builder.ins().sextend(I64, a);
                let b = self.builder.ins().sextend(I64, b);
                let (value, _) = self.builder.ins().smul_overflow(a, b);
                let (value, _) = self.builder.ins().sadd_overflow(value, c);
                let width = self.operand_width(&instruction.operands()[0]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SMAX => todo!(),
            Op::SMAXV => todo!(),
            Op::SMC => todo!(),
            Op::SMIN => todo!(),
            Op::SMINV => todo!(),
            Op::SMLAL => todo!(),
            Op::SMLAL2 => todo!(),
            Op::SMLSL => todo!(),
            Op::SMLSL2 => todo!(),
            Op::SMMLA => todo!(),
            Op::SMOPA => todo!(),
            Op::SMOPS => todo!(),
            Op::SMOV => todo!(),
            Op::SMSTART => todo!(),
            Op::SMSTOP => todo!(),
            Op::SMSUBL => {
                // Signed Multiply-Subtract Long

                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let a = self.translate_operand(&instruction.operands()[3]);
                let n = self.builder.ins().sextend(I64, n);
                let m = self.builder.ins().sextend(I64, m);
                let (value, _) = self.builder.ins().smul_overflow(n, m);
                let value = self.builder.ins().isub(a, value);
                let width = Width::_64;
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SMNEGL => {
                // Signed multiply-negate long

                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let a = self.builder.ins().iconst(I64, 0);
                let n = self.builder.ins().sextend(I64, n);
                let m = self.builder.ins().sextend(I64, m);
                let (value, _) = self.builder.ins().smul_overflow(n, m);
                let value = self.builder.ins().isub(a, value);
                let width = Width::_64;
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SMULH => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().smulhi(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SMULL => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let a = self.builder.ins().sextend(I64, a);
                let b = self.builder.ins().sextend(I64, b);
                let (value, _) = self.builder.ins().smul_overflow(a, b);
                let width = self.operand_width(&instruction.operands()[0]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::SMULL2 => todo!(),
            Op::SQDECB => todo!(),
            Op::SQDECD => todo!(),
            Op::SQDECH => todo!(),
            Op::SQDECP => todo!(),
            Op::SQDECW => todo!(),
            Op::SQDMLAL => todo!(),
            Op::SQDMLAL2 => todo!(),
            Op::SQDMLSL => todo!(),
            Op::SQDMLSL2 => todo!(),
            Op::SQDMULL => todo!(),
            Op::SQDMULL2 => todo!(),
            Op::SQINCB => todo!(),
            Op::SQINCD => todo!(),
            Op::SQINCH => todo!(),
            Op::SQINCP => todo!(),
            Op::SQINCW => todo!(),
            Op::SQRSHRN2 => todo!(),
            Op::SQRSHRUN2 => todo!(),
            Op::SQSHRN => todo!(),
            Op::SQSHRN2 => todo!(),
            Op::SQSHRUN => todo!(),
            Op::SQSHRUN2 => todo!(),
            Op::SQXTN => todo!(),
            Op::SQXTN2 => todo!(),
            Op::SQXTUN => todo!(),
            Op::SQXTUN2 => todo!(),
            Op::SSBB => todo!(),
            Op::SSHL => todo!(),
            Op::SSHLL => todo!(),
            Op::SSHLL2 => todo!(),
            Op::SSHR => todo!(),
            Op::SSUBL => todo!(),
            Op::SSUBL2 => todo!(),
            Op::SSUBW => todo!(),
            Op::SSUBW2 => todo!(),
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
            Op::STLUR => todo!(),
            Op::STLURB => todo!(),
            Op::STLURH => todo!(),
            Op::STXP | Op::STLXP => {
                // [ref:atomics]: We don't model semantics (yet).
                let status_target = get_destination_register!();
                let width = self.operand_width(&instruction.operands()[1]);
                let data1 = self.translate_operand(&instruction.operands()[1]);
                let data2 = self.translate_operand(&instruction.operands()[2]);
                let target = self.translate_operand(&instruction.operands()[3]);
                monitor!(store_excl target, status_target,
                    self.generate_write(target, data1, width);
                    let target = self
                        .builder
                        .ins()
                        .iadd_imm(target, i64::from(width as i32) / 8);
                    self.generate_write(target, data2, width);
                );
                write_back!();
            }
            Op::STLXRB => {
                // [ref:atomics]: We don't model semantics (yet).
                // [ref:needs_unit_test]
                let status_target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                monitor!(store_excl target, status_target,
                    let value = self.builder.ins().ireduce(I8, value);
                    self.generate_write(target, value, Width::_8);
                );
                write_back!();
            }
            Op::STLXRH => {
                // [ref:atomics]: We don't model semantics (yet).
                // [ref:needs_unit_test]
                let status_target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                monitor!(store_excl target, status_target,
                    let value = self.builder.ins().ireduce(I16, value);
                    self.generate_write(target, value, Width::_16);
                );
                write_back!();
            }
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
            Op::STTR => {
                let value = self.translate_operand(&instruction.operands()[0]);
                let target = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[0]);
                self.generate_write_unprivileged(target, value, width);
                write_back!();
            }
            Op::STTRB => {
                let value = self.translate_operand(&instruction.operands()[0]);
                let target = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().ireduce(I8, value);
                self.generate_write_unprivileged(target, value, Width::_8);
                write_back!();
            }
            Op::STTRH => {
                let value = self.translate_operand(&instruction.operands()[0]);
                // Reduce 32-bit register to least significant halfword.
                let value = self.builder.ins().ireduce(I16, value);
                let target = self.translate_operand(&instruction.operands()[1]);
                self.generate_write_unprivileged(target, value, Width::_16);
                write_back!();
            }
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
            Op::STUR => {
                let value = self.translate_operand(&instruction.operands()[0]);
                let target = self.translate_operand(&instruction.operands()[1]);
                let width = self.operand_width(&instruction.operands()[0]);
                self.generate_write(target, value, width);
                write_back!();
            }
            Op::STURB => {
                // [ref:needs_unit_test]
                let value = self.translate_operand(&instruction.operands()[0]);
                let target = self.translate_operand(&instruction.operands()[1]);
                let value = self.builder.ins().ireduce(I8, value);
                self.generate_write(target, value, Width::_8);
                write_back!();
            }
            Op::STLXR | Op::STXR => {
                // [ref:atomics]: We don't model semantics (yet).
                let status_target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                let width = self.operand_width(&instruction.operands()[1]);
                monitor!(store_excl target, status_target,
                    self.generate_write(target, value, width);
                );
                write_back!();
            }
            Op::STXRB => {
                // [ref:atomics]: We don't model semantics (yet).
                let status_target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                monitor!(store_excl target, status_target,
                    let value = self.builder.ins().ireduce(I8, value);
                    self.generate_write(target, value, Width::_8);
                );
                write_back!();
            }
            Op::STXRH => {
                // [ref:atomics]: We don't model semantics (yet).
                let status_target = get_destination_register!();
                let value = self.translate_operand(&instruction.operands()[1]);
                let target = self.translate_operand(&instruction.operands()[2]);
                monitor!(store_excl target, status_target,
                    let value = self.builder.ins().ireduce(I16, value);
                    self.generate_write(target, value, Width::_16);
                );
                write_back!();
            }
            Op::STZ2G => todo!(),
            Op::STZG => todo!(),
            Op::STZGM => todo!(),
            Op::SUBHN => todo!(),
            Op::SUBHN2 => todo!(),
            Op::SUBP => todo!(),
            Op::SUBPS => todo!(),
            Op::SUBR => todo!(),
            Op::SUDOT => todo!(),
            Op::SUMOPA => todo!(),
            Op::SUMOPS => todo!(),
            Op::SUNPKHI => todo!(),
            Op::SUNPKLO => todo!(),
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
            Op::SXTL => {
                let target = get_destination_register!();
                let target_element_size = Width::from(target.element.unwrap());
                let (source_reg, source_element_size) = match instruction.operands()[1] {
                    bad64::Operand::Reg { reg, arrspec } => (reg, Width::from(arrspec.unwrap())),
                    other => unexpected_operand!(other),
                };
                let source_value = self.simd_reg_to_value(&source_reg, None);
                let elements = i64::from(i32::from(target.width) / i32::from(target_element_size));

                let mut value = self.simd_iconst(target.width, 0);
                for i in 0..elements {
                    let elem = self.get_elem(source_value, i, source_element_size);
                    let elem = self.builder.ins().sextend(target_element_size.into(), elem);
                    value = self.set_elem(value, i, target_element_size, elem);
                }
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: target.width,
                    }
                );
            }
            Op::SXTL2 => todo!(),
            Op::SYS => todo!(),
            Op::SYSL => todo!(),
            Op::TBNZ => {
                let value = self.translate_operand(&instruction.operands()[0]);
                let bit_field = match instruction.operands()[1] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(imm),
                        shift: _,
                    } => imm,
                    other => unexpected_operand!(other),
                };
                let bit_mask = {
                    let width = self.operand_width(&instruction.operands()[0]);
                    self.builder.ins().iconst(width.into(), 1 << bit_field)
                };
                let result = self.builder.ins().band(value, bit_mask);
                let label = match instruction.operands()[2] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => unexpected_operand!(other),
                };
                let is_not_zero_value = self.builder.ins().icmp_imm(IntCC::NotEqual, result, 0);
                let is_not_zero_value = self.builder.ins().uextend(I64, is_not_zero_value);
                self.branch_if_non_zero(is_not_zero_value, label);
            }
            Op::TBZ => {
                let value = self.translate_operand(&instruction.operands()[0]);
                let bit_field = match instruction.operands()[1] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(imm),
                        shift: _,
                    } => imm,
                    other => unexpected_operand!(other),
                };
                let bit_mask = {
                    let width = self.operand_width(&instruction.operands()[0]);
                    self.builder.ins().iconst(width.into(), 1 << bit_field)
                };
                let result = self.builder.ins().band(value, bit_mask);
                let label = match instruction.operands()[2] {
                    bad64::Operand::Label(bad64::Imm::Unsigned(imm)) => imm,
                    other => unexpected_operand!(other),
                };
                let is_zero_value =
                    self.builder
                        .ins()
                        .icmp_imm(cranelift::prelude::IntCC::Equal, result, 0);
                let is_zero_value = self.builder.ins().uextend(I64, is_zero_value);
                self.branch_if_non_zero(is_zero_value, label);
            }
            Op::TCANCEL => todo!(),
            Op::TCOMMIT => todo!(),
            Op::TLBI => {
                // TLB invalidate operation
                let sigref = {
                    let mut sig = self.module.make_signature();
                    sig.params.push(AbiParam::new(self.pointer_type));
                    self.builder.import_signature(sig)
                };
                let func = self
                    .builder
                    .ins()
                    .iconst(I64, crate::memory::mmu::tlbi as usize as u64 as i64);
                let call = self
                    .builder
                    .ins()
                    .call_indirect(sigref, func, &[self.machine_ptr]);
                _ = self.builder.inst_results(call);
            }
            Op::TRN1 => todo!(),
            Op::TRN2 => todo!(),
            Op::TSB => todo!(),
            Op::TST => {
                // Test bits, setting the condition flags and discarding the result
                let a = self.translate_operand(&instruction.operands()[0]);
                let b = self.translate_operand(&instruction.operands()[1]);
                let (_result, nzcv) = ands!(a, b);
                self.update_nzcv(nzcv);
            }
            Op::TSTART => todo!(),
            Op::TTEST => todo!(),
            Op::UABAL => todo!(),
            Op::UABAL2 => todo!(),
            Op::UABD => todo!(),
            Op::UABDL => todo!(),
            Op::UABDL2 => todo!(),
            Op::UADDL => todo!(),
            Op::UADDL2 => todo!(),
            Op::UADDLP => todo!(),
            Op::UADDLV => todo!(),
            Op::UADDV => todo!(),
            Op::UADDW => todo!(),
            Op::UADDW2 => todo!(),
            Op::UBFIZ => {
                let destination = get_destination_register!();
                let source = self.translate_operand(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let masked = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(wmask),
                        shift: None,
                    } => self
                        .builder
                        .ins()
                        .band_imm(source, 2_i64.pow(wmask as u32) - 1),
                    other => unexpected_operand!(other),
                };
                let result = self.builder.ins().ishl_imm(masked, lsb);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(
                    destination,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::UBFM => todo!(),
            Op::UBFX => {
                let destination = get_destination_register!();
                let source = self.translate_operand(&instruction.operands()[1]);
                let lsb: i64 = match instruction.operands()[2] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(lsb),
                        shift: None,
                    } => lsb.try_into().unwrap(),
                    other => unexpected_operand!(other),
                };
                let result = match instruction.operands()[3] {
                    bad64::Operand::Imm32 {
                        imm: bad64::Imm::Unsigned(wmask),
                        shift: None,
                    } => self
                        .builder
                        .ins()
                        .band_imm(source, (2_i64.pow(wmask as u32) - 1) << lsb),
                    other => unexpected_operand!(other),
                };
                let result = self.builder.ins().ushr_imm(result, lsb);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(
                    destination,
                    TypedValue {
                        value: result,
                        width,
                    },
                );
            }
            Op::UCVTF => todo!(),
            Op::UDF => {
                return self.throw_undefined();
            }
            Op::UDIVR => todo!(),
            Op::UDOT => todo!(),
            Op::UMAX => todo!(),
            Op::UMAXV => todo!(),
            Op::UMIN => todo!(),
            Op::UMINV => todo!(),
            Op::UMLAL => todo!(),
            Op::UMLAL2 => todo!(),
            Op::UMLSL => todo!(),
            Op::UMLSL2 => todo!(),
            Op::UMMLA => todo!(),
            Op::UMOPA => todo!(),
            Op::UMOPS => todo!(),
            Op::UMSUBL => {
                // Unsigned Multiply-Subtract Long
                // multiplies two 32-bit register values,
                // subtracts the product from a 64-bit register value, and writes the result to
                // the 64-bit destination register.

                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let a = self.translate_operand(&instruction.operands()[3]);
                let n = self.builder.ins().uextend(I64, n);
                let m = self.builder.ins().uextend(I64, m);
                let value = self.builder.ins().imul(n, m);
                let value = self.builder.ins().isub(a, value);
                let width = Width::_64;
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::UMNEGL => {
                // Unsigned multiply-negate long
                // This instruction multiplies two 32-bit register values, negates the product,
                // and writes the result to the 64-bit destination register.
                // This is an alias of UMSUBL.

                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let n = self.translate_operand(&instruction.operands()[1]);
                let m = self.translate_operand(&instruction.operands()[2]);
                let a = self.builder.ins().iconst(I64, 0);
                let n = self.builder.ins().uextend(I64, n);
                let m = self.builder.ins().uextend(I64, m);
                let value = self.builder.ins().imul(n, m);
                let value = self.builder.ins().isub(a, value);
                let width = Width::_64;
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::UMULH => {
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let value = self.builder.ins().umulhi(a, b);
                let width = self.operand_width(&instruction.operands()[1]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::UMULL => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let a = self.builder.ins().uextend(I64, a);
                let b = self.builder.ins().uextend(I64, b);
                let value = self.builder.ins().imul(a, b);
                let width = self.operand_width(&instruction.operands()[0]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::UMADDL => {
                // [ref:needs_unit_test]
                let destination = get_destination_register!();
                let a = self.translate_operand(&instruction.operands()[1]);
                let b = self.translate_operand(&instruction.operands()[2]);
                let c = self.translate_operand(&instruction.operands()[3]);
                let a = self.builder.ins().uextend(I64, a);
                let b = self.builder.ins().uextend(I64, b);
                let value = self.builder.ins().imul(a, b);
                let value = self.builder.ins().iadd(value, c);
                let width = self.operand_width(&instruction.operands()[0]);
                write_to_register!(destination, TypedValue { value, width });
            }
            Op::UMULL2 => todo!(),
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
            Op::UQRSHRN2 => todo!(),
            Op::UQSHRN => todo!(),
            Op::UQSHRN2 => todo!(),
            Op::UQXTN => todo!(),
            Op::UQXTN2 => todo!(),
            Op::USDOT => todo!(),
            Op::USHL => todo!(),
            Op::USHLL => todo!(),
            Op::USHLL2 => todo!(),
            Op::USHR => todo!(),
            Op::USMMLA => todo!(),
            Op::USMOPA => todo!(),
            Op::USMOPS => todo!(),
            Op::USUBL => todo!(),
            Op::USUBL2 => todo!(),
            Op::USUBW => todo!(),
            Op::USUBW2 => todo!(),
            Op::UUNPKHI => todo!(),
            Op::UUNPKLO => todo!(),
            Op::UXTB => todo!(),
            Op::UXTH => todo!(),
            Op::UXTL => {
                let target = get_destination_register!();
                let target_element_size = Width::from(target.element.unwrap());
                let (source_reg, source_element_size) = match instruction.operands()[1] {
                    bad64::Operand::Reg { reg, arrspec } => (reg, Width::from(arrspec.unwrap())),
                    other => unexpected_operand!(other),
                };
                let source_value = self.simd_reg_to_value(&source_reg, None);
                let elements = i64::from(i32::from(target.width) / i32::from(target_element_size));

                let mut value = self.simd_iconst(target.width, 0);
                for i in 0..elements {
                    let elem = self.get_elem(source_value, i, source_element_size);
                    let elem = self.builder.ins().uextend(target_element_size.into(), elem);
                    value = self.set_elem(value, i, target_element_size, elem);
                }
                write_to_register!(
                    target,
                    TypedValue {
                        value,
                        width: target.width,
                    }
                );
            }
            Op::UXTL2 => todo!(),
            Op::UXTW => todo!(),
            Op::UZP1 => todo!(),
            Op::UZP2 => todo!(),
            Op::WFE => {
                let false_val = self.builder.ins().iconst(I8, i64::from(false));
                self.builder.ins().store(
                    TRUSTED_MEMFLAGS,
                    false_val,
                    self.machine_ptr,
                    std::mem::offset_of!(Armv8AMachine, cpu_state.monitor.event_register) as i32,
                );
                return self.r#yield(ExitRequestID::Yield);
            }
            Op::WFI => {
                return self.r#yield(ExitRequestID::WaitForInterrupt);
            }
            Op::WFIT | Op::WFET => {
                // FEAT_WFxT
                return self.throw_undefined();
            }
            Op::CFINV => {
                // FEAT_FlagM
                todo!()
            }
            Op::AXFLAG | Op::XAFLAG => {
                // FEAT_FlagM2
                todo!()
            }
            Op::XTN | Op::XTN2 => {
                // FEAT_AdvSIMD
                todo!()
            }
            Op::YIELD => {
                return self.r#yield(ExitRequestID::Yield);
            }
            Op::COMPACT | Op::WRFFR => {
                //FEAT_SVE
                todo!()
            }
            Op::WHILEGE
            | Op::WHILEGT
            | Op::WHILEHI
            | Op::WHILEHS
            | Op::SABA
            | Op::SHADD
            | Op::SHSUB
            | Op::SHSUBR
            | Op::SLI
            | Op::SQABS
            | Op::SQADD
            | Op::SQDMULH
            | Op::SQNEG
            | Op::SQRDMLAH
            | Op::SQRDMLSH
            | Op::SQRDMULH
            | Op::SQRSHL
            | Op::SQRSHLR
            | Op::SQSHL
            | Op::SQSHLR
            | Op::SQSHLU
            | Op::SQSUB
            | Op::SQSUBR
            | Op::SRHADD
            | Op::SRI
            | Op::SRSHL
            | Op::SRSHLR
            | Op::SRSHR
            | Op::SRSRA
            | Op::SSRA
            | Op::SUQADD
            | Op::UABA
            | Op::UHADD
            | Op::UHSUB
            | Op::UHSUBR
            | Op::UQADD
            | Op::UQRSHL
            | Op::UQRSHLR
            | Op::UQSHL
            | Op::UQSHLR
            | Op::UQSUB
            | Op::UQSUBR
            | Op::URECPE
            | Op::URHADD
            | Op::URSHL
            | Op::URSHLR
            | Op::URSHR
            | Op::URSQRTE
            | Op::URSRA
            | Op::USQADD
            | Op::USRA
            | Op::SABALB
            | Op::SABALT
            | Op::SABDLB
            | Op::SABDLT
            | Op::SADDLB
            | Op::SADDLT
            | Op::SADDWB
            | Op::SADDWT
            | Op::SMLALB
            | Op::SMLALT
            | Op::SMLSLB
            | Op::SMLSLT
            | Op::SMULLB
            | Op::SMULLT
            | Op::SQDMLALB
            | Op::SQDMLALT
            | Op::SQDMLSLB
            | Op::SQDMLSLT
            | Op::SQDMULLB
            | Op::SQDMULLT
            | Op::SSHLLB
            | Op::SSHLLT
            | Op::SSUBLB
            | Op::SSUBLT
            | Op::SSUBWB
            | Op::SSUBWT
            | Op::UABALB
            | Op::UABALT
            | Op::UABDLB
            | Op::UABDLT
            | Op::UADDLB
            | Op::UADDLT
            | Op::UADDWB
            | Op::UADDWT
            | Op::UMLALB
            | Op::UMLALT
            | Op::UMLSLB
            | Op::UMLSLT
            | Op::UMULLB
            | Op::UMULLT
            | Op::USHLLB
            | Op::USHLLT
            | Op::USUBLB
            | Op::USUBLT
            | Op::USUBWB
            | Op::USUBWT
            | Op::ADDHNB
            | Op::ADDHNT
            | Op::RADDHNB
            | Op::RADDHNT
            | Op::RSHRNB
            | Op::RSHRNT
            | Op::RSUBHNB
            | Op::RSUBHNT
            | Op::SHRNB
            | Op::SHRNT
            | Op::SQRSHRNB
            | Op::SQRSHRNT
            | Op::SQRSHRUNB
            | Op::SQRSHRUNT
            | Op::SQSHRNB
            | Op::SQSHRNT
            | Op::SQSHRUNB
            | Op::SQSHRUNT
            | Op::SUBHNB
            | Op::SUBHNT
            | Op::UQRSHRNB
            | Op::UQRSHRNT
            | Op::UQSHRNB
            | Op::UQSHRNT
            | Op::SQXTNB
            | Op::SQXTNT
            | Op::SQXTUNB
            | Op::SQXTUNT
            | Op::UQXTNB
            | Op::UQXTNT
            | Op::ADDP
            | Op::FADDP
            | Op::FMAXNMP
            | Op::FMAXP
            | Op::FMINNMP
            | Op::FMINP
            | Op::SMAXP
            | Op::SMINP
            | Op::UMINP
            | Op::SADALP
            | Op::UADALP
            | Op::BCAX
            | Op::BSL
            | Op::BSL1N
            | Op::BSL2N
            | Op::EOR3
            | Op::NBSL
            | Op::XAR
            | Op::ADCLB
            | Op::ADCLT
            | Op::SBCLB
            | Op::SBCLT
            | Op::MLA
            | Op::MLS
            | Op::CADD
            | Op::CMLA
            | Op::SQCADD
            | Op::SQRDCMLAH
            | Op::SADDLBT
            | Op::SQDMLALBT
            | Op::SQDMLSLBT
            | Op::SSUBLBT
            | Op::SSUBLTB
            | Op::CDOT
            | Op::FCVTLT
            | Op::FCVTNT
            | Op::FCVTX
            | Op::FCVTXNT
            | Op::BFCVTN
            | Op::FCVTN
            | Op::FMLALB
            | Op::FMLALT
            | Op::FMLSLB
            | Op::FMLSLT
            | Op::FLOGB
            | Op::HISTCNT
            | Op::HISTSEG
            | Op::MATCH
            | Op::NMATCH
            | Op::WHILERW
            | Op::WHILEWR
            | Op::BDEP
            | Op::BEXT
            | Op::BGRP
            | Op::EORBT
            | Op::EORTB
            | Op::PMUL
            | Op::PMULLB
            | Op::PMULLT
            | Op::SPLICE
            | Op::TBL
            | Op::TBX
            | Op::AESD
            | Op::AESE
            | Op::AESIMC
            | Op::AESMC
            | Op::RAX1
            | Op::SM4E
            | Op::SM4EKEY
            | Op::SCLAMP
            | Op::UCLAMP
            | Op::SQRSHRN
            | Op::SQRSHRUN
            | Op::UQRSHRN
            | Op::CNTP
            | Op::PTRUE
            | Op::WHILELE
            | Op::WHILELO
            | Op::WHILELS
            | Op::WHILELT
            | Op::REVD => {
                // FEAT_SVE2
                todo!()
            }
            Op::ADDVA | Op::ADDHA => {
                // FEAT_SME
                todo!()
            }
            Op::CLASTA
            | Op::CLASTB
            | Op::BRKA
            | Op::BRKAS
            | Op::BRKB
            | Op::BRKBS
            | Op::BRKN
            | Op::BRKNS
            | Op::BRKPA
            | Op::BRKPAS
            | Op::BRKPB
            | Op::BRKPBS
            | Op::ASRR
            | Op::ASRD
            | Op::ANDV
            | Op::ADDVL
            | Op::ADDPL
            | Op::ZIP1
            | Op::ZIP2
            | Op::CNTB
            | Op::CNTD
            | Op::CNTH
            | Op::CNTW
            | Op::CMPEQ
            | Op::CMPGE
            | Op::CMPGT
            | Op::CMPHI
            | Op::CMPHS
            | Op::CMPLE
            | Op::CMPLO
            | Op::CMPLS
            | Op::CMPLT
            | Op::CMPNE
            | Op::CNOT
            | Op::CTERMEQ
            | Op::CTERMNE
            | Op::DECB
            | Op::DECD
            | Op::DECH
            | Op::DECP
            | Op::DECW => {
                // FEAT_SVE || FEAT_SME
                todo!()
            }
            Op::BFMLAL | Op::ZERO => {
                // FEAT_SME2
                todo!()
            }
            Op::CMPP | Op::ADDG | Op::GMI | Op::IRG | Op::SUBG => {
                // FEAT_MTE
                todo!()
            }
        }
        ControlFlow::Continue(())
    }

    /// Save state and exit to lookup function
    fn unconditional_jump_epilogue(&mut self, dest_label: Value) -> ControlFlow<Option<BlockExit>> {
        // [ref:can_trap]: Check `dest_label` alignment.
        {
            let pc = self.builder.ins().iconst(I64, self.address as i64);
            self.builder.ins().store(
                TRUSTED_MEMFLAGS,
                pc,
                self.machine_ptr,
                std::mem::offset_of!(Armv8AMachine, prev_pc) as i32,
            );
        }
        self.store_pc(Some(dest_label));
        ControlFlow::Break(Some(BlockExit::Branch(dest_label)))
    }

    /// Save state and call a simulans function that stops execution
    fn emit_indirect_noreturn(
        &mut self,
        pc: u64,
        sig: codegen::ir::SigRef,
        callee: codegen::ir::Value,
        args: &[Value],
    ) -> ControlFlow<Option<BlockExit>> {
        self.store_pc(None);
        _ = self.indirect_call(pc, sig, callee, args);
        ControlFlow::Break(Some(BlockExit::Exception))
    }

    /// Yield
    fn r#yield(&mut self, id: ExitRequestID) -> ControlFlow<Option<BlockExit>> {
        extern "C" fn set_exit_request(machine: &mut Armv8AMachine, id: ExitRequestID) {
            *machine.cpu_state.exit_request.lock().unwrap() = Some(id.into());
        }

        let sigref = {
            let mut sig = self.module.make_signature();
            sig.params.push(AbiParam::new(self.pointer_type));
            sig.params.push(AbiParam::new(I8));
            self.builder.import_signature(sig)
        };
        let func = self
            .builder
            .ins()
            .iconst(I64, set_exit_request as usize as u64 as i64);
        let next_pc = self.builder.ins().iconst(I64, self.address as i64 + 4);
        let id = self.builder.ins().iconst(I8, i64::from(id as u8));
        let ret = self.emit_indirect_noreturn(self.address, sigref, func, &[self.machine_ptr, id]);
        self.store_pc(Some(next_pc));
        ret
    }

    /// Throw Undefined exception
    fn throw_undefined(&mut self) -> ControlFlow<Option<BlockExit>> {
        let sigref = {
            let mut sig = self.module.make_signature();
            sig.params.push(AbiParam::new(self.pointer_type));
            sig.params.push(AbiParam::new(self.pointer_type));
            self.builder.import_signature(sig)
        };
        let func = self.builder.ins().iconst(
            I64,
            crate::exceptions::aarch64_undefined as usize as u64 as i64,
        );
        let pc = self.builder.ins().iconst(I64, self.address as i64);
        self.emit_indirect_noreturn(self.address, sigref, func, &[self.machine_ptr, pc])
    }

    /// Save state and call a helper function
    fn indirect_call(
        &mut self,
        pc: u64,
        sig: codegen::ir::SigRef,
        callee: codegen::ir::Value,
        args: &[Value],
    ) -> &[Value] {
        self.save_cpu_state();
        let pc = self.builder.ins().iconst(I64, pc as i64);
        self.builder.ins().store(
            TRUSTED_MEMFLAGS,
            pc,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, prev_pc) as i32,
        );
        self.store_pc(Some(pc));
        let call = self.builder.ins().call_indirect(sig, callee, args);
        // Restore state
        self.load_cpu_state(false);
        self.builder.inst_results(call)
    }

    fn direct_exit(&mut self, block_exit: BlockExit) {
        self.save_cpu_state();
        let prev_pc = self.builder.ins().iconst(I64, self.address as i64);
        self.builder.ins().store(
            TRUSTED_MEMFLAGS,
            prev_pc,
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, prev_pc) as i32,
        );
        if let BlockExit::Branch(v) = block_exit {
            self.store_pc(Some(v));
        }
        let translate_func = self
            .builder
            .ins()
            .iconst(I64, lookup_block as usize as u64 as i64);
        self.builder.ins().return_(&[translate_func]);
    }

    /// Generate JIT instructions to assign a variable for each register and set
    /// it with its value.
    ///
    /// Used as a preamble to a translation block.
    fn load_cpu_state(&mut self, declare: bool) {
        use bad64::Reg;

        use crate::cpu_state::RegisterFile;

        {
            let var = if declare {
                assert!(!self.registers.contains_key(&Reg::SP));
                let var = self.builder.declare_var(I64);
                self.registers.insert(Reg::SP, var);
                var
            } else {
                self.registers[&Reg::SP]
            };
            let value = sysregs::SP::generate_read(self);
            self.builder.def_var(var, value);
        }

        macro_rules! reg_field {
            ($($field:ident => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = self.builder.ins().iadd_imm(self.machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    let value = self.builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, i32::try_from(offset).unwrap());
                    let var = if declare {
                        assert!(!self.registers.contains_key(&$bad_reg));
                        let var = self.builder.declare_var(I64);
                        self.registers.insert($bad_reg, var);
                        var
                    } else {
                        self.registers[&$bad_reg]
                    };
                    self.builder.def_var(var, value);
                )*
            }};
            (sys $($field:ident => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let addr = self.builder.ins().iadd_imm(self.machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    let value = self.builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, i32::try_from(offset).unwrap());
                    let var = if declare {
                        assert!(!self.sys_registers.contains_key(&$bad_sys_reg));
                        let var = self.builder.declare_var(I64);
                        self.sys_registers.insert($bad_sys_reg, var);
                        var
                    } else {
                        self.sys_registers[&$bad_sys_reg]
                    };
                    self.builder.def_var(var, value);
                )*
            }};
        }
        reg_field! { sys
            spsr_el3 =>  SysReg::SPSR_EL3,
            spsr_el1 => SysReg::SPSR_EL1,
        }
        reg_field! {
            x0 => Reg::X0,
            x1 => Reg::X1,
            x2 => Reg::X2,
            x3 => Reg::X3,
            x4 => Reg::X4,
            x5 => Reg::X5,
            x6 => Reg::X6,
            x7 => Reg::X7,
            x8 => Reg::X8,
            x9 => Reg::X9,
            x10 => Reg::X10,
            x11 => Reg::X11,
            x12 => Reg::X12,
            x13 => Reg::X13,
            x14 => Reg::X14,
            x15 => Reg::X15,
            x16 => Reg::X16,
            x17 => Reg::X17,
            x18 => Reg::X18,
            x19 => Reg::X19,
            x20 => Reg::X20,
            x21 => Reg::X21,
            x22 => Reg::X22,
            x23 => Reg::X23,
            x24 => Reg::X24,
            x25 => Reg::X25,
            x26 => Reg::X26,
            x27 => Reg::X27,
            x28 => Reg::X28,
            x29 => Reg::X29,
            x30 => Reg::X30,
        }
        {
            let zero = self.builder.ins().iconst(I64, 0);
            let var = if declare {
                debug_assert!(!self.registers.contains_key(&Reg::XZR));
                let var = self.builder.declare_var(I64);
                self.registers.insert(Reg::XZR, var);
                var
            } else {
                self.registers[&Reg::XZR]
            };
            self.builder.def_var(var, zero);
        }
        let vector_addr = self.builder.ins().iadd_imm(
            self.machine_ptr,
            std::mem::offset_of!(Armv8AMachine, cpu_state.vector_registers) as i64,
        );
        for i in 0_u32..=31 {
            let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
            let offset = i * std::mem::size_of::<u128>() as u32;
            let offset = i32::try_from(offset).unwrap();
            let v_value =
                self.builder
                    .ins()
                    .load(I128, TRUSTED_MEMFLAGS, vector_addr, offset as i32);
            let v_var = if declare {
                assert!(!self.registers.contains_key(&v_reg));
                let v_var = self.builder.declare_var(I128);
                self.registers.insert(v_reg, v_var);
                v_var
            } else {
                self.registers[&v_reg]
            };
            self.builder.def_var(v_var, v_value);
        }
    }

    /// Generate JIT instructions to store register values back to `self`.
    ///
    /// Used as an epilogue of a translation block.
    pub fn save_cpu_state(&mut self) {
        use bad64::Reg;

        use crate::cpu_state::RegisterFile;

        {
            let var = self.registers[&Reg::SP];
            let var_value = self.builder.use_var(var);
            sysregs::SP::generate_write(self, var_value);
        }

        macro_rules! reg_field {
            ($($field:ident => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = self.builder.ins().iadd_imm(self.machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    assert!(self.registers.contains_key(&$bad_reg));
                    let var = &self.registers[&$bad_reg];
                    let var_value = self.builder.use_var(*var);
                    self.builder.ins().store(TRUSTED_MEMFLAGS, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
            (sys $($field:ident$($conversion:expr)? => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let addr = self.builder.ins().iadd_imm(self.machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    assert!(self.sys_registers.contains_key(&$bad_sys_reg));
                    let var = &self.sys_registers[&$bad_sys_reg];
                    let var_value = self.builder.use_var(*var);
                    self.builder.ins().store(TRUSTED_MEMFLAGS, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
        }

        if self.write_to_sysreg {
            reg_field! { sys
                spsr_el3 =>  SysReg::SPSR_EL3,
                spsr_el1 => SysReg::SPSR_EL1,
            };
        }
        reg_field! {
            x0 => Reg::X0,
            x1 => Reg::X1,
            x2 => Reg::X2,
            x3 => Reg::X3,
            x4 => Reg::X4,
            x5 => Reg::X5,
            x6 => Reg::X6,
            x7 => Reg::X7,
            x8 => Reg::X8,
            x9 => Reg::X9,
            x10 => Reg::X10,
            x11 => Reg::X11,
            x12 => Reg::X12,
            x13 => Reg::X13,
            x14 => Reg::X14,
            x15 => Reg::X15,
            x16 => Reg::X16,
            x17 => Reg::X17,
            x18 => Reg::X18,
            x19 => Reg::X19,
            x20 => Reg::X20,
            x21 => Reg::X21,
            x22 => Reg::X22,
            x23 => Reg::X23,
            x24 => Reg::X24,
            x25 => Reg::X25,
            x26 => Reg::X26,
            x27 => Reg::X27,
            x28 => Reg::X28,
            x29 => Reg::X29,
            x30 => Reg::X30,
        }
        if self.write_to_simd {
            let vector_addr = self.builder.ins().iadd_imm(
                self.machine_ptr,
                std::mem::offset_of!(Armv8AMachine, cpu_state.vector_registers) as i64,
            );
            for i in 0_u32..=31 {
                let offset = i * std::mem::size_of::<u128>() as u32;
                let offset = i32::try_from(offset).unwrap();
                let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
                assert!(self.registers.contains_key(&v_reg));
                let var = &self.registers[&v_reg];
                let value = self.builder.use_var(*var);
                self.builder
                    .ins()
                    .store(TRUSTED_MEMFLAGS, value, vector_addr, offset);
            }
        }
    }

    #[inline]
    fn def_view(&mut self, view: &TypedRegisterView, value: Value) {
        self.builder.def_var(view.var, value);
    }
}
