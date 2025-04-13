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

use crate::memory::MemorySize;

pub const FDT_MAX_SIZE: u64 = 0x200000;

pub const fn calculate_fdt_offset(phys_mem_start: u64, mem_size: MemorySize) -> usize {
    (phys_mem_start + mem_size.get() - FDT_MAX_SIZE - 0x10000) as usize
}

pub struct FdtBuilder {
    pub phys_mem_start: u64,
    pub cmdline: Option<String>,
    pub mem_size: MemorySize,
    pub num_vcpus: NonZero<u32>,
}

impl FdtBuilder {
    pub fn build(self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        let mut fdt = FdtWriter::new()?;

        let root_node = fdt.begin_node("")?;
        // [ref:TODO][ref:serial]: add serial support, either uart or HVC

        // [ref:TODO][ref:interrupts]: add gic support
        // fdt.property_u32("interrupt-parent", phandle_gic)?;
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
            let mem_reg_prop = [self.phys_mem_start, self.mem_size.get()];

            let memory_node = fdt.begin_node("memory")?;
            fdt.property_string("device_type", "memory")?;
            fdt.property_array_u64("reg", &mem_reg_prop)?;
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

        Ok(fdt.finish()?)
    }
}
