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

use std::num::NonZero;

use vm_fdt::FdtWriter;

use crate::memory::{Address, MemoryRegion, MemorySize};

pub const FDT_MAX_SIZE: u64 = 0x200000;

#[derive(Clone, Debug)]
pub struct Fdt {
    pub bytes: Vec<u8>,
    pub address: Address,
}

pub struct FdtBuilder {
    phys_mem_start: Address,
    phys_mem_end: Address,
    fdt_offset: Address,
    cmdline: Option<String>,
    mem_size: MemorySize,
    num_vcpus: NonZero<u32>,
}

impl FdtBuilder {
    pub fn new(
        region: &MemoryRegion,
        mem_size: MemorySize,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        if region.last_addr().0 <= (FDT_MAX_SIZE + 0x10000_u64) {
            return Err(format!(
                "FDT max size {} cannot fit into region of size {}",
                MemorySize((FDT_MAX_SIZE + 0x10000_u64).try_into().unwrap()),
                region.size
            )
            .into());
        }
        let fdt_offset = region.last_addr() - FDT_MAX_SIZE - 0x10000_u64;
        Ok(Self {
            fdt_offset,
            phys_mem_start: region.start_addr(),
            phys_mem_end: region.last_addr(),
            cmdline: None,
            mem_size,
            num_vcpus: NonZero::new(1).unwrap(),
        })
    }

    pub const fn num_vcpus(mut self, num_vcpus: NonZero<u32>) -> Self {
        self.num_vcpus = num_vcpus;
        self
    }

    pub fn cmdline(mut self, cmdline: Option<String>) -> Self {
        self.cmdline = cmdline;
        self
    }

    pub fn build(self) -> Result<Fdt, Box<dyn std::error::Error>> {
        let mut fdt = FdtWriter::new()?;

        let root_node = fdt.begin_node("")?;
        // [ref:TODO][ref:serial]: add pl011 node, if present
        // [ref:TODO][ref:serial]: implement hypervisor calls?

        // [ref:TODO][ref:interrupts]: add gic support
        // fdt.property_u32("interrupt-parent", phandle_gic)?;
        fdt.property_null("dma-coherent")?;
        fdt.property_string("model", "linux,dummy-virt")?;
        fdt.property_string("compatible", "linux,dummy-virt")?;
        fdt.property_u32("#address-cells", 0x2)?;
        fdt.property_u32("#size-cells", 0x2)?;

        {
            let cmdline = self.cmdline.as_deref().unwrap_or("");
            let chosen_node = fdt.begin_node("chosen")?;
            fdt.property_string("bootargs", cmdline)?;
            fdt.end_node(chosen_node)?;
        }

        {
            let mem_reg_prop = [self.phys_mem_start.0, self.mem_size.get()];

            let memory_node = fdt.begin_node("memory")?;
            fdt.property_array_u64("reg", &mem_reg_prop)?;
            fdt.property_string("device_type", "memory")?;
            fdt.end_node(memory_node)?;
        }
        {
            let cpus_node = fdt.begin_node("cpus")?;
            fdt.property_u32("#address-cells", 0x1)?;
            fdt.property_u32("#size-cells", 0x0)?;

            for cpu_id in 0..self.num_vcpus.get() {
                let cpu_name = format!("cpu@{:x}", cpu_id);
                let cpu_node = fdt.begin_node(&cpu_name)?;
                fdt.property_string("device_type", "cpu")?;
                fdt.property_string("compatible", "arm,arm-v8")?;
                fdt.property_string("enable-method", "psci")?;
                fdt.property_u32("reg", cpu_id)?;
                fdt.end_node(cpu_node)?;
            }
            fdt.end_node(cpus_node)?;
        }
        {
            let psci_node = fdt.begin_node("psci")?;
            fdt.property_string("compatible", "arm,psci-0.2")?;
            fdt.property_string("method", "hvc")?;
            fdt.end_node(psci_node)?;
        }
        fdt.end_node(root_node)?;

        let fdt = fdt.finish()?;
        if self.fdt_offset + fdt.len() > self.phys_mem_end {
            return Err(format!(
                "fdt_offset {} plus fdt size {} bytes (total: {} bytes) is larger than DRAM \
                 memory size of {} bytes",
                self.fdt_offset,
                fdt.len(),
                self.fdt_offset + fdt.len(),
                MemorySize(
                    (self.phys_mem_end.0 - self.phys_mem_start.0)
                        .try_into()
                        .unwrap()
                )
            )
            .into());
        }
        Ok(Fdt {
            bytes: fdt,
            address: self.fdt_offset,
        })
    }
}
