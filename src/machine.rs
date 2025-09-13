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

use std::{
    collections::BTreeSet,
    num::NonZero,
    pin::Pin,
    sync::{
        atomic::{AtomicU8, Ordering},
        Arc,
    },
};

use crate::{
    cpu_state::*,
    jit::{lookup_entry, Entry},
    memory::*,
    tracing,
};

mod entry_blocks;
pub use entry_blocks::{EntryBlock, EntryBlocks};

#[repr(C)]
pub struct ResolvedAddress<'a> {
    pub mem_region: &'a MemoryRegion,
    pub address_inside_region: u64,
}

pub extern "C" fn address_lookup(machine: &mut Armv8AMachine, address: u64) -> ResolvedAddress<'_> {
    tracing::event!(
        target: tracing::TraceItem::AddressLookup.as_str(),
        tracing::Level::TRACE,
        address = ?Address(address),
        pc = ?Address(machine.pc),
    );
    let Some(mem_region) = machine.memory.find_region(Address(address)) else {
        panic!(
            "Could not look up address {} in physical memory map. pc was: 0x{:x}",
            Address(address),
            machine.pc
        );
    };
    let address_inside_region = address - mem_region.phys_offset.0;
    ResolvedAddress {
        mem_region,
        address_inside_region,
    }
}

pub extern "C" fn helper_set_exit_request(machine: &mut Armv8AMachine, exit_request: u8) {
    machine.exit_request.store(exit_request, Ordering::SeqCst);
}

/// The state of the emulated machine.
#[repr(C)]
pub struct Armv8AMachine {
    pub pc: u64,
    pub prev_pc: u64,
    pub cpu_state: ExecutionState,
    pub memory: MemoryMap,
    pub lookup_entry_func: Entry,
    pub hw_breakpoints: BTreeSet<Address>,
    pub exit_request: Arc<AtomicU8>,
    pub in_breakpoint: bool,
}

impl Armv8AMachine {
    pub fn new(memory: MemoryMap) -> Pin<Box<Self>> {
        let exit_request = Arc::new(AtomicU8::new(0));
        Self::new_with_exit_request(memory, exit_request)
    }

    pub fn new_with_exit_request(memory: MemoryMap, exit_request: Arc<AtomicU8>) -> Pin<Box<Self>> {
        Box::pin(Self {
            pc: 0,
            prev_pc: 0,
            cpu_state: ExecutionState::default(),
            memory,
            lookup_entry_func: Entry(lookup_entry),
            hw_breakpoints: BTreeSet::new(),
            exit_request,
            in_breakpoint: false,
        })
    }

    /// Generates a flattened device tree
    ///
    /// This function will:
    ///
    /// 1. Generate a flattened device tree blob
    /// 2. Map it to the guest memory
    /// 3. Write a bootloader code at address `0x4` that passes a pointer to the
    ///    fdt at register `x0` and jumps to `entry_point`.
    ///
    /// Returns the generated fdt on success.
    pub fn generate_fdt(
        &mut self,
        entry_point: Address,
    ) -> Result<crate::fdt::Fdt, Box<dyn std::error::Error>> {
        let fdt = crate::fdt::FdtBuilder::new(&self.memory)?
            .num_vcpus(NonZero::new(1).unwrap())
            .cmdline(None)
            .build()?;

        self.load_code(&fdt.bytes, fdt.address)?;

        let bootloader = Armv8ABootloader {
            entry_point,
            fdt_address: fdt.address,
        };
        bootloader.write_to_memory(Address(0x4), self)?;
        self.pc = 0x4;

        Ok(fdt)
    }

    /// Load code to physical memory address.
    pub fn load_code(
        &mut self,
        input: &[u8],
        address: Address,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let Some(input_size) = NonZero::new(input.len().try_into()?) else {
            tracing::info!("Called `load_code` with empty slice which does nothing.");
            return Ok(());
        };
        let Some(mem_region) = self.memory.find_region_mut(address) else {
            return Err(format!(
                "Cannot load code to address {} which is not covered by a RAM memory region.",
                address
            )
            .into());
        };

        if address + input.len() > mem_region.last_addr() {
            return Err(format!(
                "Input of size {} cannot fit in DRAM of size {} starting from address {}.",
                MemorySize(input_size),
                mem_region.len(),
                address
            )
            .into());
        }
        let address_inside_region = address.0 - mem_region.phys_offset.0;
        tracing::trace!(
            "loading code of {} in address {} (address inside region of size {} is {})",
            MemorySize((input.len() as u64).try_into().unwrap()),
            address,
            mem_region.size,
            Address(address_inside_region)
        );
        let Some(mmapped_region) = mem_region.as_mmap_mut() else {
            return Err(format!(
                "Cannot load code to address {} which is mapped to device memory",
                address
            )
            .into());
        };

        // SAFETY: We performed boundary checks in the above check.
        unsafe {
            std::ptr::copy_nonoverlapping(
                input.as_ptr(),
                mmapped_region
                    .as_mut_ptr()
                    .add(address_inside_region as usize),
                input.len(),
            )
        };
        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Armv8ABootloader {
    pub entry_point: Address,
    pub fdt_address: Address,
}

impl Armv8ABootloader {
    pub fn write_to_memory(
        self,
        destination: Address,
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
            lower_32bit!(self.fdt_address.0), // arg: .word @dtb lower 32bit
            /* 1c: */
            higher_32bit!(self.fdt_address.0), // .word @dtb higher 32bit
            /* 20: */
            lower_32bit!(self.entry_point.0), // entry: .word @kernel entry lower 32bit
            /* 24: */
            higher_32bit!(self.entry_point.0), // .word @kernel entry higher 32bit
        ];
        // SAFETY: integers can be re-interpreted as bytes.
        let byte_slice = unsafe { std::mem::transmute::<[u32; 10], [u8; 10 * 4]>(code) };
        machine.load_code(&byte_slice, destination)
    }
}
