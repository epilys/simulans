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

//! Representation of an emulated machine.

use std::{num::NonZero, pin::Pin};

use rustc_hash::FxHashMap;

use crate::{
    cpu_state::*,
    jit::{lookup_entry, Entry},
    memory::*,
};

/// The state of the emulated machine.
#[repr(C)]
pub struct Armv8AMachine {
    pub pc: u64,
    pub prev_pc: u64,
    pub cpu_state: ExecutionState,
    pub mem: MemoryRegion,
    pub entry_blocks: FxHashMap<u64, Entry>,
    pub lookup_entry_func: Entry,
    pub halted: u8,
}

impl Armv8AMachine {
    pub fn new(memory_size: MemorySize) -> Pin<Box<Self>> {
        let mem = MemoryRegion::new("ram", memory_size, PHYS_MEM_START as usize).unwrap();
        let mut cpu_state = ExecutionState::default();
        cpu_state.registers.sp = mem.phys_offset as u64 + memory_size.get() / 2;
        let entry_blocks = FxHashMap::default();
        Box::pin(Self {
            pc: 0,
            prev_pc: 0,
            cpu_state,
            mem,
            entry_blocks,
            lookup_entry_func: Entry(lookup_entry),
            halted: 0,
        })
    }

    pub fn generate_fdt(&mut self, entry_point: Address) -> Result<(), Box<dyn std::error::Error>> {
        let fdt_offset =
            crate::fdt::calculate_fdt_offset(crate::memory::PHYS_MEM_START, self.mem.size);
        let fdt = crate::fdt::FdtBuilder {
            phys_mem_start: crate::memory::PHYS_MEM_START,
            cmdline: None,
            mem_size: self.mem.size,
            num_vcpus: NonZero::new(1).unwrap(),
        }
        .build()?;
        if fdt_offset > self.mem.len() {
            return Err(format!(
                "fdt_offset 0x{fdt_offset:x} ({} bytes) is larger than memory size of {} bytes",
                fdt_offset,
                self.mem.len()
            )
            .into());
        }
        if fdt_offset + fdt.len() > self.mem.len() {
            return Err(format!(
                "fdt_offset 0x{fdt_offset:x} plus fdt size {} bytes (total: {} bytes) is larger \
                 than memory size of {} bytes",
                fdt.len(),
                fdt_offset + fdt.len(),
                self.mem.len()
            )
            .into());
        }
        self.load_code(&fdt, fdt_offset)?;

        let bootloader = Armv8ABootloader {
            entry_point,
            dtb_ptr: Address(fdt_offset.try_into()?),
        };
        bootloader.write_to_memory(0x4, self)?;
        self.pc = 0x4;

        Ok(())
    }

    /// Load code to physical memory address.
    pub fn load_code(
        &mut self,
        input: &[u8],
        address: usize,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let Some(input_size) = NonZero::new(input.len().try_into()?) else {
            log::info!("Called `load_code` with empty slice which does nothing.");
            return Ok(());
        };
        if address < self.mem.phys_offset {
            return Err(format!(
                "Cannot load code to address {} which is below start of DRAM {}.",
                Address(address as u64),
                Address(self.mem.phys_offset as u64),
            )
            .into());
        }
        if (address - self.mem.phys_offset) >= self.mem.len() {
            return Err(format!(
                "Address {} does not fit into DRAM of size {}.",
                Address(address as u64),
                self.mem.size
            )
            .into());
        }
        if (address + input.len() - self.mem.phys_offset) >= self.mem.len() {
            return Err(format!(
                "Input of size {} cannot fit in DRAM of size {} starting from address {}.",
                MemorySize(input_size),
                self.mem.size,
                Address(address as u64),
            )
            .into());
        }
        let address_inside_region = address - self.mem.phys_offset;

        // SAFETY: We performed boundary checks in the above check.
        unsafe {
            std::ptr::copy_nonoverlapping(
                input.as_ptr(),
                self.mem.map.as_mut_ptr().add(address_inside_region),
                input.len(),
            )
        };
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Armv8ABootloader {
    pub entry_point: Address,
    pub dtb_ptr: Address,
}

impl Armv8ABootloader {
    pub fn write_to_memory(
        self,
        destination: usize,
        machine: &mut Armv8AMachine,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // ```shell
        // $ cstool -a arm64 --mode default --endian little  --code c0000058e1031faae2031faae3031faa8400005880001fd6 --addr 0`
        // 0:   c0 00 00 58    ldr     x0, #0x18
        // 4:   e1 03 1f aa    mov     x1, xzr
        // 8:   e2 03 1f aa    mov     x2, xzr
        // c:   e3 03 1f aa    mov     x3, xzr
        // 10:  84 00 00 58    ldr     x4, #0x20
        // 14:  80 00 1f d6    br x4
        // ```
        macro_rules! lower_32bit {
            ($value:expr) => {{
                ($value & u64::from(u32::MAX)) as u32
            }};
        }
        macro_rules! higher_32bit {
            ($value:expr) => {{
                ($value >> 32) as u32
            }};
        }
        let code: [u32; 10] = [
            /* 0: */
            0xc0_00_00_58_u32.swap_bytes(), /* `ldr x0, #0x18`, equiv to `ldr x0, =arg`
                                             * pseudo-instruction (PC-relative address) */
            /* 4: */ 0xe1_03_1f_aa_u32.swap_bytes(), // `mov x1, xzr`
            /* 8: */ 0xe2_03_1f_aa_u32.swap_bytes(), // `mov x2, xzr`
            /* c: */ 0xe3_03_1f_aa_u32.swap_bytes(), // `mov x3, xzr`
            /* 10: */
            0x84_00_00_58_u32.swap_bytes(), /* `ldr x4, #0x20`, equiv to `ldr x0, =entry`
                                             * pseudo-instruction (PC-relative address) */
            /* 14: */ 0x80001fd6_u32.swap_bytes(), // `br  x4`
            /* 18: */
            lower_32bit!(self.dtb_ptr.0), // arg: .word @dtb lower 32bit
            /* 1c: */
            higher_32bit!(self.dtb_ptr.0), // .word @dtb higher 32bit
            /* 20: */
            lower_32bit!(self.entry_point.0), // entry: .word @kernel entry lower 32bit
            /* 24: */
            higher_32bit!(self.entry_point.0), // .word @kernel entry higher 32bit
        ];
        // SAFETY: integers can be re-interpreted as bytes.
        let byte_slice = unsafe { std::mem::transmute::<[u32; 10], [u8; 10 * 4]>(code) };
        {
            use capstone::prelude::*;

            let mut cs = Capstone::new()
                .arm64()
                .mode(capstone::arch::arm64::ArchMode::Arm)
                .endian(capstone::Endian::Little)
                .detail(true)
                .build()
                .expect("Failed to create Capstone object");
            cs.set_syntax(capstone::Syntax::Intel)?;
            cs.set_skipdata(false)?;
            let decoded_iter = cs.disasm_all(&byte_slice, 0)?;
            eprintln!("Bootloader output:");
            for insn in decoded_iter.as_ref() {
                eprintln!("{}", insn);
            }
            eprintln!("Bootloader output done");
        }
        machine.load_code(&byte_slice, destination)
    }
}
