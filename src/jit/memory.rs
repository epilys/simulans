// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Memory access operations

use cranelift::{
    codegen::ir::{
        entities::StackSlot,
        instructions::BlockArg,
        stackslot::{StackSlotData, StackSlotKind},
        types::{I128, I16, I32, I64, I8},
    },
    prelude::*,
};
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::{
    jit::{lookup_block, BlockTranslator},
    memory::{mmu::ResolvedAddress, Width},
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
    /// Generates a JIT write access
    pub fn generate_write(&mut self, target_address: Value, value: Value, width: Width) -> Value {
        let address_lookup_func = self.builder.ins().iconst(
            I64,
            crate::memory::mmu::translate_address as usize as u64 as i64,
        );
        self.store_pc(None);
        let preferred_exception_return = self.builder.ins().iconst(I64, self.address as i64);
        let raise_exception = self.builder.ins().iconst(I8, i64::from(true));
        let (resolved_address_slot, resolved_address_slot_address) =
            create_stack_slot!(self, ResolvedAddress<'_>);
        let call = self.builder.ins().call_indirect(
            self.address_lookup_sigref,
            address_lookup_func,
            &[
                self.machine_ptr,
                target_address,
                preferred_exception_return,
                raise_exception,
                resolved_address_slot_address,
            ],
        );
        let (success, memory_region_ptr, address_inside_region) = {
            let success = self.builder.inst_results(call)[0];
            let memory_region_ptr = self.builder.ins().stack_load(
                self.module.target_config().pointer_type(),
                resolved_address_slot,
                std::mem::offset_of!(ResolvedAddress, mem_region) as i32,
            );
            let address_inside_region = self.builder.ins().stack_load(
                I64,
                resolved_address_slot,
                std::mem::offset_of!(ResolvedAddress, address_inside_region) as i32,
            );
            (success, memory_region_ptr, address_inside_region)
        };
        let success_block = self.builder.create_block();
        let failure_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, I8);
        self.builder
            .ins()
            .brif(success, success_block, &[], failure_block, &[]);
        self.builder.switch_to_block(success_block);
        self.builder.seal_block(success_block);

        let (write_func, sigref) = self.memops_table.write(width);
        let write_func = self.builder.ins().iconst(I64, write_func);
        let call = self.builder.ins().call_indirect(
            *sigref,
            write_func,
            &[memory_region_ptr, address_inside_region, value],
        );
        self.builder.inst_results(call);
        self.builder
            .ins()
            .jump(merge_block, &[BlockArg::from(success)]);
        self.builder.switch_to_block(failure_block);
        self.builder.seal_block(failure_block);
        let translate_func = self
            .builder
            .ins()
            .iconst(I64, lookup_block as usize as u64 as i64);
        self.builder.ins().return_(&[translate_func]);
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        let success = self.builder.block_params(merge_block)[0];
        success
    }

    #[inline]
    /// Generates a JIT read access
    pub fn generate_read(&mut self, target_address: Value, width: Width) -> Value {
        let address_lookup_func = self.builder.ins().iconst(
            I64,
            crate::memory::mmu::translate_address as usize as u64 as i64,
        );
        self.store_pc(None);
        let preferred_exception_return = self.builder.ins().iconst(I64, self.address as i64);
        let raise_exception = self.builder.ins().iconst(I8, i64::from(true));
        let (resolved_address_slot, resolved_address_slot_address) =
            create_stack_slot!(self, ResolvedAddress<'_>);
        let call = self.builder.ins().call_indirect(
            self.address_lookup_sigref,
            address_lookup_func,
            &[
                self.machine_ptr,
                target_address,
                preferred_exception_return,
                raise_exception,
                resolved_address_slot_address,
            ],
        );
        let (read_value_slot, read_value_slot_address) = create_stack_slot!(self, width = width);
        let (success, resolved) = {
            let success = self.builder.inst_results(call)[0];
            let memory_region_ptr = self.builder.ins().stack_load(
                self.module.target_config().pointer_type(),
                resolved_address_slot,
                std::mem::offset_of!(ResolvedAddress, mem_region) as i32,
            );
            let address_inside_region = self.builder.ins().stack_load(
                I64,
                resolved_address_slot,
                std::mem::offset_of!(ResolvedAddress, address_inside_region) as i32,
            );
            (
                success,
                [
                    memory_region_ptr,
                    address_inside_region,
                    read_value_slot_address,
                ],
            )
        };
        let success_block = self.builder.create_block();
        let failure_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, width.into());
        self.builder
            .ins()
            .brif(success, success_block, &[], failure_block, &[]);
        self.builder.switch_to_block(success_block);
        self.builder.seal_block(success_block);

        let (read_func, sigref) = self.memops_table.read(width);
        let read_func = self.builder.ins().iconst(I64, read_func);
        let _call = self
            .builder
            .ins()
            .call_indirect(*sigref, read_func, &resolved);
        let read_value = self
            .builder
            .ins()
            .stack_load(width.into(), read_value_slot, 0);
        self.builder
            .ins()
            .jump(merge_block, &[BlockArg::from(read_value)]);
        self.builder.switch_to_block(failure_block);
        self.builder.seal_block(failure_block);
        let translate_func = self
            .builder
            .ins()
            .iconst(I64, lookup_block as usize as u64 as i64);
        self.builder.ins().return_(&[translate_func]);
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);
        self.builder.block_params(merge_block)[0]
    }
}

/// Helper struct to hold signatures for memory operation callbacks (see
/// [`crate::memory::ops`])
pub struct MemOpsTable {
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
                crate::memory::ops::memory_region_write_8 as usize as u64 as i64,
                &self.write_sigrefs[0],
            ),
            Width::_16 => (
                crate::memory::ops::memory_region_write_16 as usize as u64 as i64,
                &self.write_sigrefs[1],
            ),
            Width::_32 => (
                crate::memory::ops::memory_region_write_32 as usize as u64 as i64,
                &self.write_sigrefs[2],
            ),
            Width::_64 => (
                crate::memory::ops::memory_region_write_64 as usize as u64 as i64,
                &self.write_sigrefs[3],
            ),
            Width::_128 => (
                crate::memory::ops::memory_region_write_128 as usize as u64 as i64,
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
                crate::memory::ops::memory_region_read_8 as usize as u64 as i64,
                &self.read_sigrefs[0],
            ),
            Width::_16 => (
                crate::memory::ops::memory_region_read_16 as usize as u64 as i64,
                &self.read_sigrefs[1],
            ),
            Width::_32 => (
                crate::memory::ops::memory_region_read_32 as usize as u64 as i64,
                &self.read_sigrefs[2],
            ),
            Width::_64 => (
                crate::memory::ops::memory_region_read_64 as usize as u64 as i64,
                &self.read_sigrefs[3],
            ),
            Width::_128 => (
                crate::memory::ops::memory_region_read_128 as usize as u64 as i64,
                &self.read_sigrefs[4],
            ),
        }
    }

    /// Create new [`MemOpsTable`].
    pub fn new(module: &JITModule, builder: &mut FunctionBuilder<'_>) -> Self {
        macro_rules! sigref {
            (write $t:expr) => {{
                let mut sig = module.make_signature();
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                sig.params.push(AbiParam::new($t));
                builder.import_signature(sig)
            }};
            (read $t:expr) => {{
                let mut sig = module.make_signature();
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                sig.params
                    .push(AbiParam::new(module.target_config().pointer_type()));
                builder.import_signature(sig)
            }};
        }
        let write_sigrefs = [
            sigref! { write I8 },
            sigref! { write I16 },
            sigref! { write I32 },
            sigref! { write I64 },
            sigref! { write I128 },
        ];

        let read_sigrefs = [
            sigref! { read I8 },
            sigref! { read I16 },
            sigref! { read I32 },
            sigref! { read I64 },
            sigref! { read I128 },
        ];

        Self {
            write_sigrefs,
            read_sigrefs,
        }
    }
}
