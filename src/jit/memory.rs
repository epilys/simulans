// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Memory access operations

use cranelift::{
    codegen::ir::types::{I128, I16, I32, I64, I8},
    prelude::*,
};
use cranelift_jit::JITModule;
use cranelift_module::Module;

use crate::{jit::BlockTranslator, memory::Width};

impl BlockTranslator<'_> {
    #[inline]
    /// Generates a JIT write access
    pub fn generate_write(&mut self, target_address: Value, value: Value, width: Width) {
        let (write_func, sigref) = self.memops_table.write(width);
        let address_lookup_func = self.builder.ins().iconst(
            I64,
            crate::machine::physical_address_lookup as usize as u64 as i64,
        );
        let call = self.builder.ins().call_indirect(
            self.address_lookup_sigref,
            address_lookup_func,
            &[self.machine_ptr, target_address],
        );
        let (memory_region_ptr, address_inside_region) = {
            let results = self.builder.inst_results(call);
            (results[0], results[1])
        };
        let write_func = self.builder.ins().iconst(I64, write_func);
        let call = self.builder.ins().call_indirect(
            *sigref,
            write_func,
            &[memory_region_ptr, address_inside_region, value],
        );
        self.builder.inst_results(call);
    }

    #[inline]
    /// Generates a JIT read access
    pub fn generate_read(&mut self, target_address: Value, width: Width) -> Value {
        let (read_func, sigref) = self.memops_table.read(width);
        let address_lookup_func = self.builder.ins().iconst(
            I64,
            crate::machine::physical_address_lookup as usize as u64 as i64,
        );
        let call = self.builder.ins().call_indirect(
            self.address_lookup_sigref,
            address_lookup_func,
            &[self.machine_ptr, target_address],
        );
        let resolved = {
            let results = self.builder.inst_results(call);
            [results[0], results[1]]
        };
        let read_func = self.builder.ins().iconst(I64, read_func);
        let call = self
            .builder
            .ins()
            .call_indirect(*sigref, read_func, &resolved);
        self.builder.inst_results(call)[0]
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
                sig.returns.push(AbiParam::new($t));
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
