// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Memory access operations

use cranelift::{
    codegen::ir::{
        entities::StackSlot,
        stackslot::{StackSlotData, StackSlotKind},
        types::{I128, I16, I32, I64, I8},
    },
    prelude::*,
};
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::{
    cpu_state::ExitRequest,
    jit::{BlockExit, BlockTranslator},
    memory::Width,
};

macro_rules! create_stack_slot {
    ($self:expr, width = $w:expr) => {{
        match $w {
            Width::_8 => create_stack_slot!($self, u8),
            Width::_16 => create_stack_slot!($self, u16),
            Width::_32 => create_stack_slot!($self, u32),
            Width::_64 => create_stack_slot!($self, u64),
            Width::_128 => create_stack_slot!($self, u128),
        }
    }};
    ($self:expr, $t:ty) => {{
        let stack_slot: StackSlot = $self.builder.create_sized_stack_slot(StackSlotData::new(
            StackSlotKind::ExplicitSlot,
            std::mem::size_of::<$t>().try_into().unwrap(),
            std::mem::align_of::<$t>().try_into().unwrap(),
        ));
        let addr = $self.builder.ins().stack_addr(
            $self.module.target_config().pointer_type(),
            stack_slot,
            0,
        );
        (stack_slot, addr)
    }};
}

impl BlockTranslator<'_> {
    #[inline]
    /// Generates a privileged JIT write access
    pub fn generate_write(&mut self, target_address: Value, value: Value, width: Width) -> Value {
        self.generate_write_inner(target_address, value, width, false)
    }

    #[inline]
    /// Generates an unprivileged JIT write access
    pub fn generate_write_unprivileged(
        &mut self,
        target_address: Value,
        value: Value,
        width: Width,
    ) -> Value {
        self.generate_write_inner(target_address, value, width, true)
    }

    #[inline]
    /// Generates a JIT write access
    fn generate_write_inner(
        &mut self,
        target_address: Value,
        value: Value,
        width: Width,
        unprivileged: bool,
    ) -> Value {
        self.store_pc(None);
        let preferred_exception_return = self.builder.ins().iconst(I64, self.address as i64);
        let unprivileged = self.builder.ins().iconst(I8, i64::from(unprivileged));
        let (_exception_slot, exception_slot_address) = create_stack_slot!(self, ExitRequest);
        let (write_func, sigref) = self.memops_table.write(width);
        let write_func = self.builder.ins().iconst(I64, write_func);
        let call = self.builder.ins().call_indirect(
            *sigref,
            write_func,
            &[
                self.machine_ptr,
                target_address,
                value,
                unprivileged,
                preferred_exception_return,
                exception_slot_address,
            ],
        );
        let success = self.builder.inst_results(call)[0];
        let success_block = self.builder.create_block();
        let failure_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(success, success_block, &[], failure_block, &[]);
        self.builder.switch_to_block(failure_block);
        self.builder.seal_block(failure_block);
        _ = self.builder.ins().call_indirect(
            self.memops_table.set_exception_sigref,
            self.set_exception_func,
            &[self.machine_ptr, exception_slot_address],
        );
        self.store_pc(None);
        self.direct_exit(BlockExit::Exception);
        self.builder.switch_to_block(success_block);
        self.builder.seal_block(success_block);
        success
    }

    #[inline]
    /// Generates a privileged JIT read access
    pub fn generate_read(&mut self, target_address: Value, width: Width) -> Value {
        self.generate_read_inner(target_address, width, false)
    }

    #[inline]
    /// Generates an unprivileged JIT read access
    pub fn generate_read_unprivileged(&mut self, target_address: Value, width: Width) -> Value {
        self.generate_read_inner(target_address, width, true)
    }

    #[inline]
    /// Generates a JIT read access
    fn generate_read_inner(
        &mut self,
        target_address: Value,
        width: Width,
        unprivileged: bool,
    ) -> Value {
        self.store_pc(None);
        let preferred_exception_return = self.builder.ins().iconst(I64, self.address as i64);
        let unprivileged = self.builder.ins().iconst(I8, i64::from(unprivileged));
        let (read_value_slot, read_value_slot_address) = create_stack_slot!(self, width = width);
        let (_exception_slot, exception_slot_address) = create_stack_slot!(self, ExitRequest);
        let (read_func, sigref) = self.memops_table.read(width);
        let read_func = self.builder.ins().iconst(I64, read_func);
        let call = self.builder.ins().call_indirect(
            *sigref,
            read_func,
            &[
                self.machine_ptr,
                target_address,
                read_value_slot_address,
                unprivileged,
                preferred_exception_return,
                exception_slot_address,
            ],
        );
        let success = self.builder.inst_results(call)[0];
        let success_block = self.builder.create_block();
        let failure_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(success, success_block, &[], failure_block, &[]);
        self.builder.switch_to_block(failure_block);
        self.builder.seal_block(failure_block);
        _ = self.builder.ins().call_indirect(
            self.memops_table.set_exception_sigref,
            self.set_exception_func,
            &[self.machine_ptr, exception_slot_address],
        );
        self.store_pc(None);
        self.direct_exit(BlockExit::Exception);
        self.builder.switch_to_block(success_block);
        self.builder.seal_block(success_block);
        self.builder
            .ins()
            .stack_load(width.into(), read_value_slot, 0)
    }
}

/// Helper struct to hold signatures for memory operation callbacks (see
/// [`crate::memory::mmu::ops`])
pub struct MemOpsTable {
    set_exception_sigref: codegen::ir::SigRef,
    write_sigrefs: [codegen::ir::SigRef; 5],
    read_sigrefs: [codegen::ir::SigRef; 5],
}

impl MemOpsTable {
    #[inline]
    /// Returns appropriate function pointer and signature for a specific width
    /// memory write
    fn write(&self, width: Width) -> (i64, &codegen::ir::SigRef) {
        match width {
            Width::_8 => (
                crate::memory::mmu::ops::write_8 as usize as u64 as i64,
                &self.write_sigrefs[0],
            ),
            Width::_16 => (
                crate::memory::mmu::ops::write_16 as usize as u64 as i64,
                &self.write_sigrefs[1],
            ),
            Width::_32 => (
                crate::memory::mmu::ops::write_32 as usize as u64 as i64,
                &self.write_sigrefs[2],
            ),
            Width::_64 => (
                crate::memory::mmu::ops::write_64 as usize as u64 as i64,
                &self.write_sigrefs[3],
            ),
            Width::_128 => (
                crate::memory::mmu::ops::write_128 as usize as u64 as i64,
                &self.write_sigrefs[4],
            ),
        }
    }

    #[inline]
    /// Returns appropriate function pointer and signature for a specific width
    /// memory read
    fn read(&self, width: Width) -> (i64, &codegen::ir::SigRef) {
        match width {
            Width::_8 => (
                crate::memory::mmu::ops::read_8 as usize as u64 as i64,
                &self.read_sigrefs[0],
            ),
            Width::_16 => (
                crate::memory::mmu::ops::read_16 as usize as u64 as i64,
                &self.read_sigrefs[1],
            ),
            Width::_32 => (
                crate::memory::mmu::ops::read_32 as usize as u64 as i64,
                &self.read_sigrefs[2],
            ),
            Width::_64 => (
                crate::memory::mmu::ops::read_64 as usize as u64 as i64,
                &self.read_sigrefs[3],
            ),
            Width::_128 => (
                crate::memory::mmu::ops::read_128 as usize as u64 as i64,
                &self.read_sigrefs[4],
            ),
        }
    }

    /// Create new [`MemOpsTable`].
    pub fn new(module: &JITModule, builder: &mut FunctionBuilder<'_>) -> Self {
        macro_rules! sigref {
            (read $t:expr) => {{
                let mut sig = module.make_signature();
                // machine: &Armv8AMachine,
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                // address: Address,
                sig.params.push(AbiParam::new(I64));
                // ret: &mut MaybeUninit<$size>,
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                // unprivileged: bool,
                sig.params.push(AbiParam::new(I8));
                // preferred_exception_return: Address,
                sig.params.push(AbiParam::new(I64));
                // exception: &mut MaybeUninit<ExitRequest>,
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                // -> bool
                sig.returns.push(AbiParam::new(I8));
                builder.import_signature(sig)
            }};
            (write $t:expr) => {{
                let mut sig = module.make_signature();
                // machine: &mut Armv8AMachine,
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                // address: Address,
                sig.params.push(AbiParam::new(I64));
                // value: $size,
                sig.params.push(AbiParam::new($t));
                // unprivileged: bool,
                sig.params.push(AbiParam::new(I8));
                // preferred_exception_return: Address,
                sig.params.push(AbiParam::new(I64));
                // exception: &mut MaybeUninit<ExitRequest>,
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                // -> bool
                sig.returns.push(AbiParam::new(I8));
                builder.import_signature(sig)
            }};
        }
        let (read_sigrefs, write_sigrefs) = (
            [
                sigref! { read I8 },
                sigref! { read I16 },
                sigref! { read I32 },
                sigref! { read I64 },
                sigref! { read I128 },
            ],
            [
                sigref! { write I8 },
                sigref! { write I16 },
                sigref! { write I32 },
                sigref! { write I64 },
                sigref! { write I128 },
            ],
        );

        let set_exception_sigref = {
            let mut sig = module.make_signature();
            sig.params
                .push(AbiParam::new(module.target_config().pointer_type()));
            sig.params
                .push(AbiParam::new(module.target_config().pointer_type()));
            builder.import_signature(sig)
        };
        Self {
            set_exception_sigref,
            write_sigrefs,
            read_sigrefs,
        }
    }
}
