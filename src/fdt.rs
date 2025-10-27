// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Flattened device-tree (FDT) blob generation.

use std::{collections::BTreeMap, num::NonZero};

pub use vm_fdt::FdtWriter;

use crate::memory::{Address, DeviceID, MemoryMap, MemorySize};

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

#[derive(Copy, Clone, Debug)]
pub struct DeviceMemoryDescription {
    pub device_memory_id: u64,
    pub phys_offset: Address,
    pub size: MemorySize,
}

#[derive(Clone, Debug)]
pub struct FdtContext {
    pub phandle_clk: u32,
    pub phandle_gic: u32,
    pub phandle: u32,
    pub memory_regions: Vec<DeviceMemoryDescription>,
}

#[derive(Clone, Debug)]
pub enum NodeKind {
    Stdout(String),
    InterruptController,
    Clock,
}

pub trait DeviceTreeExt: crate::devices::DeviceOps {
    fn kind(&self) -> Option<NodeKind>;
    fn insert(
        &self,
        ctx: &FdtContext,
        writer: &mut FdtWriter,
    ) -> Result<(), Box<dyn std::error::Error>>;
}

/// A builder struct for FDT blobs.
pub struct FdtBuilder<'a> {
    memory_map: &'a MemoryMap,
    bootargs: Option<String>,
    num_vcpus: NonZero<u32>,
}

impl<'a> FdtBuilder<'a> {
    /// Create new builder for `memory_map`.
    pub fn new(memory_map: &'a MemoryMap) -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Self {
            memory_map,
            bootargs: None,
            num_vcpus: NonZero::new(1).unwrap(),
        })
    }

    /// Set number of vCPUs.
    pub const fn num_vcpus(mut self, num_vcpus: NonZero<u32>) -> Self {
        self.num_vcpus = num_vcpus;
        self
    }

    /// Set `bootargs` node.
    pub fn bootargs(mut self, bootargs: Option<String>) -> Self {
        self.bootargs = bootargs;
        self
    }

    /// Generate binary blob.
    pub fn build(self) -> Result<Fdt, Box<dyn std::error::Error>> {
        let mut fdt = FdtWriter::new()?;
        let mut stdout_path = None;
        let mut device_mem_desc: BTreeMap<DeviceID, Vec<DeviceMemoryDescription>> = BTreeMap::new();

        for (r, mem_id, ops, dt_ops) in self
            .memory_map
            .iter()
            .filter_map(|r| Some((r, r.as_device()?)))
            .map(|(r, (mem_id, ops))| (r, mem_id, ops, ops.supports_device_tree()))
        {
            if let Some(dt_ops) = dt_ops {
                if let (Some(NodeKind::Stdout(node_name)), true) =
                    (dt_ops.kind(), stdout_path.is_none())
                {
                    stdout_path = Some(format!("/{node_name}@{:x?}", r.phys_offset.0));
                }
            }
            device_mem_desc
                .entry(ops.id())
                .or_default()
                .push(DeviceMemoryDescription {
                    device_memory_id: mem_id,
                    phys_offset: r.phys_offset,
                    size: r.size,
                });
        }

        let root_node = fdt.begin_node("")?;
        // [ref:TODO][ref:serial]: implement hypervisor calls?

        let phandle_clk = 0x8000;
        let phandle_gic = 0x8002;
        fdt.property_u32("interrupt-parent", phandle_gic)?;
        fdt.property_null("dma-coherent")?;
        fdt.property_string("model", "linux,dummy-virt")?;
        fdt.property_string("compatible", "linux,dummy-virt")?;
        fdt.property_u32("#address-cells", 0x2)?;
        fdt.property_u32("#size-cells", 0x2)?;

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
            let memory_node = fdt.begin_node(&format!("memory@{:x?}", region.start_addr().0))?;
            fdt.property_string("device_type", "memory")?;
            fdt.property_array_u64("reg", &mem_reg_prop)?;
            fdt.end_node(memory_node)?;
        }

        {
            let clk_node = fdt.begin_node("apb-pclk")?;
            fdt.property_u32("phandle", phandle_clk)?;
            fdt.property_string("clock-output-names", "clk24mhz")?;
            fdt.property_u32("clock-frequency", 0x16e3600)?;
            fdt.property_u32("#clock-cells", 0x00)?;
            fdt.property_string("compatible", "fixed-clock")?;
            fdt.end_node(clk_node)?;
        }
        for (ops, dt_ops) in self
            .memory_map
            .iter()
            .filter_map(|r| r.as_device())
            .filter_map(|(_, ops)| Some((ops, ops.supports_device_tree()?)))
        {
            let ctx = FdtContext {
                phandle_clk,
                phandle_gic,
                phandle: if matches!(dt_ops.kind(), Some(NodeKind::InterruptController)) {
                    phandle_gic
                } else {
                    0
                },
                memory_regions: device_mem_desc.get(&ops.id()).cloned().unwrap_or_default(),
            };
            dt_ops.insert(&ctx, &mut fdt)?;
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
            fdt.property_string_list(
                "compatible",
                vec![
                    "arm,psci-1.0".to_string(),
                    "arm,psci-0.2".to_string(),
                    "arm,psci".to_string(),
                ],
            )?;
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
        {
            let bootargs = self.bootargs.as_deref().unwrap_or("");
            let chosen_node = fdt.begin_node("chosen")?;
            fdt.property_string("bootargs", bootargs)?;
            if let Some(ref stdout_path) = stdout_path {
                fdt.property_string("stdout-path", stdout_path)?;
            }
            fdt.end_node(chosen_node)?;
        }
        {
            let aliases_node = fdt.begin_node("aliases")?;
            if let Some(ref stdout_path) = stdout_path {
                fdt.property_string("serial0", stdout_path)?;
            }
            fdt.end_node(aliases_node)?;
        }

        fdt.end_node(root_node)?;

        let fdt = fdt.finish()?;
        Ok(Fdt {
            bytes: fdt,
            address: Address(0x48000000),
        })
    }
}
