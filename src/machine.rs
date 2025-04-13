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
