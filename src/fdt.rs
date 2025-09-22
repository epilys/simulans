// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Flattened device-tree (FDT) blob generation.

use std::num::NonZero;

use vm_fdt::FdtWriter;

use crate::memory::{Address, MemoryMap};

/// Maximum allowed size in bytes.
pub const FDT_MAX_SIZE: u64 = 0x200000;

#[derive(Clone, Debug)]
/// A generated FDT.
pub struct Fdt {
    /// Blob
    pub bytes: Vec<u8>,
    /// Address to load it into.
    pub address: Address,
}

/// A builder struct for FDT blobs.
pub struct FdtBuilder<'a> {
    memory_map: &'a MemoryMap,
    cmdline: Option<String>,
    num_vcpus: NonZero<u32>,
}

impl<'a> FdtBuilder<'a> {
    /// Create new builder for `memory_map`.
    pub fn new(memory_map: &'a MemoryMap) -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Self {
            memory_map,
            cmdline: None,
            num_vcpus: NonZero::new(1).unwrap(),
        })
    }

    /// Set number of vCPUs.
    pub const fn num_vcpus(mut self, num_vcpus: NonZero<u32>) -> Self {
        self.num_vcpus = num_vcpus;
        self
    }

    /// Set `bootargs` node.
    pub fn cmdline(mut self, cmdline: Option<String>) -> Self {
        self.cmdline = cmdline;
        self
    }

    /// Generate binary blob.
    pub fn build(self) -> Result<Fdt, Box<dyn std::error::Error>> {
        let mut fdt = FdtWriter::new()?;

        let root_node = fdt.begin_node("")?;
        // [ref:TODO][ref:serial]: add pl011 node, if present
        // [ref:TODO][ref:serial]: implement hypervisor calls?

        let phandle_gic = 0x8002;
        fdt.property_u32("interrupt-parent", phandle_gic)?;
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

        for region in self.memory_map.iter() {
            let Some(mmap) = region.as_mmap() else {
                continue;
            };
            // Skip boot rom
            // [ref:TODO]: add DRAM memory type
            if mmap.read_only {
                continue;
            }
            let mem_reg_prop = [region.start_addr().0, region.len() as u64];
            let memory_node = fdt.begin_node(&format!("memory@{:X?}", region.start_addr().0))?;
            fdt.property_string("device_type", "memory")?;
            fdt.property_array_u64("reg", &mem_reg_prop)?;
            fdt.end_node(memory_node)?;
        }
        {
            // [ref:FIXME]: get address from device instance
            let gic_start = 0x8000000;

            let intc_node = fdt.begin_node(&format!("intc@{gic_start:x?}"))?;
            fdt.property_u32("phandle", phandle_gic)?;
            let reg_prop = [gic_start, 0x10000, gic_start + 0x10000, 0x10000];
            fdt.property_array_u64("reg", &reg_prop)?;
            fdt.property_string("compatible", "arm,cortex-a15-gic")?;
            fdt.property_null("ranges")?;
            fdt.property_u32("#size-cells", 0x02)?;
            fdt.property_u32("#address-cells", 0x02)?;
            fdt.property_null("interrupt-controller")?;
            fdt.property_u32("#interrupt-cells", 0x03)?;
            fdt.end_node(intc_node)?;
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
        {
            let timer_node = fdt.begin_node("timer")?;
            let interrupts = [
                0x01, 0x0d, 0x104, 0x01, 0x0e, 0x104, 0x01, 0x0b, 0x104, 0x01, 0x0a, 0x104,
            ];
            fdt.property_array_u32("interrupts", &interrupts)?;
            fdt.property_null("always-on")?;
            fdt.property_string("compatible", "arm,armv8-timer")?;
            fdt.end_node(timer_node)?;
        }
        fdt.end_node(root_node)?;

        let fdt = fdt.finish()?;
        Ok(Fdt {
            bytes: fdt,
            address: Address(0x48000000),
        })
    }
}
