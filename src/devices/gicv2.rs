// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! # ARM ® Generic Interrupt Controller Architecture version 2.0

use std::sync::{Arc, Mutex};

use crate::{
    memory::{Address, MemoryRegion, MemorySize, Width},
    tracing,
};

#[derive(Debug)]
pub struct GicV2 {
    /// Device ID.
    device_id: u64,
    dist: Address,
    cpu_if: Address,
}

impl GicV2 {
    pub fn new(device_id: u64, dist: Address, cpu_if: Address) -> Self {
        if (dist < cpu_if && dist + 0x10000_u64 > cpu_if)
            || (cpu_if < dist && cpu_if + 0x10000_u64 > dist)
        {
            panic!(
                "GicV2 distributor memory at {dist} overlaps with CPU interface memory at \
                 {cpu_if} (each is sized  0x10000 bytes)"
            );
        }
        Self {
            device_id,
            dist,
            cpu_if,
        }
    }
}

impl crate::devices::Device for GicV2 {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn into_memory_regions(self) -> Vec<MemoryRegion> {
        let Self {
            device_id,
            dist,
            cpu_if,
        } = self;
        let registers = Arc::new(Mutex::new((Gicd::new(), Gicc::new())));
        vec![
            MemoryRegion::new_io(
                MemorySize::new(0x10000).unwrap(),
                dist,
                Box::new(GicV2DistMemoryOps {
                    device_id,
                    registers: registers.clone(),
                }),
            )
            .unwrap(),
            MemoryRegion::new_io(
                MemorySize::new(0x10000).unwrap(),
                cpu_if,
                Box::new(GicV2CPUMemoryOps {
                    device_id,
                    registers,
                }),
            )
            .unwrap(),
        ]
    }
}

#[derive(Debug)]
struct GicV2DistMemoryOps {
    device_id: u64,
    registers: Arc<Mutex<(Gicd, Gicc)>>,
}

impl crate::memory::DeviceMemoryOps for GicV2DistMemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> u64 {
        // [ref:TODO]: return Error
        assert_eq!(width, Width::_32);
        let gicd = &self.registers.lock().unwrap().0;
        let field: &'static str;
        let value = match offset {
            (0x000..0x004) => {
                // GICD_CTLR RW 0x00000000 Distributor Control Register
                field = "GICD_CTLR";
                gicd.ctlr
            }
            (0x004..0x008) => {
                // GICD_TYPER RO IMPLEMENTATION DEFINED Interrupt Controller Type Register
                field = "GICD_TYPER";
                gicd.typer
            }
            (0x008..0x00c) => {
                // GICD_IIDR RO IMPLEMENTATION DEFINED Distributor Implementer Identification
                // Register
                field = "GICD_IIDR";
                gicd.iidr
            }
            (0x00C..0x020) => {
                field = "Reserved";
                0
            }
            (0x020..0x040) => {
                field = "IMPLEMENTATION DEFINED registers";
                0
            }
            (0x040..0x080) => {
                field = "Reserved";
                0
            }
            (0x080..0x084) => {
                // GICD_IGROUPRn b RW IMPLEMENTATION DEFINED c Interrupt Group Registers
                field = "GICD_IGROUPR";
                let idx = (offset - 0x080) / 0x04;
                gicd.igroupr[idx as usize]
            }
            (0x084..0x100) => {
                // x00000000
                field = "GICD_IGROUPR";
                0
            }
            (0x100..0x180) => {
                // GICD_ISENABLER RW IMPLEMENTATION DEFINED Interrupt Set-Enable Registers
                field = "GICD_ISENABLER";
                let idx = (offset - 0x100) / 0x04;
                gicd.isenabler[idx as usize]
            }
            (0x180..0x200) => {
                // GICD_ICENABLER RW IMPLEMENTATION DEFINED Interrupt Clear-Enable Registers
                field = "GICD_ICENABLER";
                let idx = (offset - 0x180) / 0x04;
                gicd.icenabler[idx as usize]
            }
            (0x200..0x280) => {
                // GICD_ISPENDR RW 0x00000000 Interrupt Set-Pending Registers
                field = "GICD_ISPENDR";
                let idx = (offset - 0x180) / 0x04;
                gicd.ispendr[idx as usize]
            }
            (0x280..0x300) => {
                // GICD_ICPENDR RW 0x00000000 Interrupt Clear-Pending Registers
                field = "GICD_ICPENDR";
                let idx = (offset - 0x280) / 0x04;
                gicd.icpendr[idx as usize]
            }
            (0x300..0x380) => {
                // GICD_ISACTIVER RW 0x00000000 GICv2 Interrupt Set-Active Registers
                field = "GICD_ISACTIVER";
                let idx = (offset - 0x300) / 0x04;
                gicd.isactiver[idx as usize]
            }
            (0x380..0x400) => {
                // GICD_ICACTIVER RW 0x00000000 Interrupt Clear-Active Registers
                field = "GICD_ICACTIVER";
                let idx = (offset - 0x380) / 0x04;
                gicd.icactiver[idx as usize]
            }
            (0x400..0x7FC) => {
                // GICD_IPRIORITYR RW 0x00000000 Interrupt Priority Registers
                field = "GICD_IPRIORITYR";
                let idx = (offset - 0x400) / 0x04;
                gicd.ipriorityr[idx as usize]
            }
            (0x7FC..0x800) => {
                field = "Reserved";
                0
            }
            (0x800..0x820) => {
                // GICD_ITARGETSR RO f IMPLEMENTATION DEFINED Interrupt Processor Targets
                // Registers
                field = "GICD_ITARGETSR";
                let idx = (offset - 0x800) / 0x04;
                gicd.itargetsr[idx as usize]
            }
            (0x820..0xBFC) => {
                // RW f 0x00000000
                field = "GICD_ITARGETSR";
                0
            }
            (0xBFC..0xC00) => {
                field = "Reserved";
                0
            }
            (0xC00..0xD00) => {
                // GICD_ICFGR RW IMPLEMENTATION DEFINED Interrupt Configuration Registers
                field = "GICD_ICFGR";
                let idx = (offset - 0xc00) / 0x04;
                gicd.icfgr[idx as usize]
            }
            (0xD00..0xE00) => {
                field = "IMPLEMENTATION DEFINED registers";
                0
            }
            (0xE00..0xF00) => {
                // GICD_NSACR RW 0x00000000 Non-secure Access Control Registers, optional
                field = "GICD_NSACR";
                0
            }
            (0xF00..0xF04) => {
                // GICD_SGIR WO - Software Generated Interrupt Register
                field = "GICD_SGIR";
                gicd.sgir
            }
            (0xF04..0xF10) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0xF10..0xF20) => {
                // GICD_CPENDSGIR RW 0x00000000 SGI Clear-Pending Registers
                field = "GICD_CPENDSGIR";
                0
            }
            (0xF20..0xF30) => {
                // GICD_SPENDSGIR RW 0x00000000 SGI Set-Pending Registers
                field = "GICD_SPENDSGIR";
                0
            }
            (0xF30..0xFD0) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0xFD0..0x1000) => {
                // - RO IMPLEMENTATION DEFINED Identification registers on page 4-119
                field = "IMPLEMENTATION DEFINED Identification registers";
                0
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
                0
            }
        }
        .into();

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            ?width,
            kind = "distributor read",
            offset = ?tracing::Hex(offset),
            field,
            value = ?tracing::BinaryHex(value),
        );

        value
    }

    fn write(&self, offset: u64, value: u64, width: Width) {
        // [ref:TODO]: return Error
        assert_eq!(width, Width::_32);
        let value = value as u32;

        let gicd = &mut self.registers.lock().unwrap().0;
        let field: &'static str;
        match offset {
            (0x000..0x004) => {
                // GICD_CTLR RW 0x00000000 Distributor Control Register
                field = "GICD_CTLR";
                gicd.ctlr = value;
            }
            (0x004..0x008) => {
                // GICD_TYPER RO IMPLEMENTATION DEFINED Interrupt Controller Type Register
                field = "GICD_TYPER";
            }
            (0x008..0x00c) => {
                // GICD_IIDR RO IMPLEMENTATION DEFINED Distributor Implementer Identification
                // Register
                field = "GICD_IIDR";
            }
            (0x00C..0x020) => {
                // Reserved
                field = "Reserved";
            }
            (0x020..0x040) => {
                field = "IMPLEMENTATION DEFINED registers";
            }
            (0x040..0x080) => {
                // Reserved
                field = "Reserved";
            }
            (0x080..0x084) => {
                // GICD_IGROUPR b RW IMPLEMENTATION DEFINED c Interrupt Group Registers
                field = "GICD_IGROUPR";
                let idx = (offset - 0x080) / 0x04;
                gicd.igroupr[idx as usize] = value;
            }
            (0x084..0x100) => {
                field = "GICD_IGROUPR";
            }
            (0x100..0x180) => {
                // GICD_ISENABLER RW IMPLEMENTATION DEFINED Interrupt Set-Enable Registers
                field = "GICD_ISENABLER";
                let idx = (offset - 0x100) / 0x04;
                gicd.isenabler[idx as usize] = value;
            }
            (0x180..0x200) => {
                // GICD_ICENABLER RW IMPLEMENTATION DEFINED Interrupt Clear-Enable Registers
                field = "GICD_ICENABLER";
                let idx = (offset - 0x180) / 0x04;
                gicd.icenabler[idx as usize] = value;
            }
            (0x200..0x280) => {
                // GICD_ISPENDR RW 0x00000000 Interrupt Set-Pending Registers
                field = "GICD_ISPENDR";
                let idx = (offset - 0x180) / 0x04;
                gicd.ispendr[idx as usize] = value;
            }
            (0x280..0x300) => {
                // GICD_ICPENDR RW 0x00000000 Interrupt Clear-Pending Registers
                field = "GICD_ICPENDR";
                let idx = (offset - 0x280) / 0x04;
                gicd.icpendr[idx as usize] = value;
            }
            (0x300..0x380) => {
                // GICD_ISACTIVER d RW 0x00000000 GICv2 Interrupt Set-Active Registers
                field = "GICD_ISACTIVER";
                let idx = (offset - 0x300) / 0x04;
                gicd.isactiver[idx as usize] = value;
            }
            (0x380..0x400) => {
                // GICD_ICACTIVER e RW 0x00000000 Interrupt Clear-Active Registers
                field = "GICD_ICACTIVER";
                let idx = (offset - 0x380) / 0x04;
                gicd.icactiver[idx as usize] = value;
            }
            (0x400..0x7FC) => {
                // GICD_IPRIORITYR RW 0x00000000 Interrupt Priority Registers
                field = "GICD_IPRIORITYR";
                let idx = (offset - 0x400) / 0x04;
                gicd.ipriorityr[idx as usize] = value;
            }
            (0x7FC..0x800) => {
                // Reserved
                field = "Reserved";
            }
            (0x800..0x820) => {
                // GICD_ITARGETSR RO f IMPLEMENTATION DEFINED Interrupt Processor Targets
                // Registers
                field = "GICD_ITARGETSR";
            }
            (0x820..0xBFC) => {
                // RW f 0x00000000
                field = "GICD_ITARGETSR";
            }
            (0xBFC..0xC00) => {
                // Reserved
                field = "Reserved";
            }
            (0xC00..0xD00) => {
                // GICD_ICFGR RW IMPLEMENTATION DEFINED Interrupt Configuration Registers
                field = "GICD_ICFGR";
                let idx = (offset - 0xc00) / 0x04;
                gicd.icfgr[idx as usize] = value;
            }
            (0xD00..0xE00) => {
                field = "IMPLEMENTATION DEFINED registers";
            }
            (0xE00..0xF00) => {
                // GICD_NSACR e RW 0x00000000 Non-secure Access Control Registers, optional
                field = "GICD_NSACR";
            }
            (0xF00..0xF04) => {
                // GICD_SGIR WO - Software Generated Interrupt Register
                field = "GICD_SGIR";
                gicd.sgir = value;
            }
            (0xF04..0xF10) => {
                // Reserved
                field = "Reserved";
            }
            (0xF10..0xF20) => {
                // GICD_CPENDSGIR e RW 0x00000000 SGI Clear-Pending Registers
                field = "GICD_CPENDSGIR";
            }
            (0xF20..0xF30) => {
                // GICD_SPENDSGIR e RW 0x00000000 SGI Set-Pending Registers
                field = "GICD_SPENDSGIR";
            }
            (0xF30..0xFD0) => {
                // Reserved
                field = "Reserved";
            }
            (0xFD0..0x1000) => {
                // - RO IMPLEMENTATION DEFINED Identification registers on page 4-119
                field = "IMPLEMENTATION DEFINED Identification registers";
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
            }
        }

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            ?width,
            kind = "distributor write",
            offset = ?tracing::Hex(offset),
            field,
            value = ?tracing::BinaryHex(value),
        );
    }
}

#[derive(Debug)]
struct GicV2CPUMemoryOps {
    device_id: u64,
    registers: Arc<Mutex<(Gicd, Gicc)>>,
}

impl crate::memory::DeviceMemoryOps for GicV2CPUMemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> u64 {
        // [ref:TODO]: return Error
        assert_eq!(width, Width::_32);
        let gicc = &self.registers.lock().unwrap().1;
        let field: &'static str;
        let value = match offset {
            (0x0000..0x0004) => {
                // GICC_CTLR RW 0x00000000 CPU Interface Control Register
                field = "GICC_CTLR";
                gicc.ctlr
            }
            (0x0004..0x0008) => {
                // GICC_PMR RW 0x00000000 Interrupt Priority Mask Register
                field = "GICC_PMR";
                gicc.pmr
            }
            (0x0008..0x000c) => {
                // GICC_BPR RW 0x0000000x a Binary Point Register
                field = "GICC_BPR";
                gicc.bpr
            }
            (0x000C..0x0010) => {
                // GICC_IAR RO 0x000003FF Interrupt Acknowledge Register
                field = "GICC_IAR";
                gicc.iar
            }
            (0x0010..0x0014) => {
                // GICC_EOIR WO - End of Interrupt Register
                field = "GICC_EOIR";
                0
            }
            (0x0014..0x0018) => {
                // GICC_RPR RO 0x000000FF Running Priority Register
                field = "GICC_RPR";
                gicc.rpr
            }
            (0x0018..0x001c) => {
                // GICC_HPPIR RO 0x000003FF Highest Priority Pending Interrupt Register
                field = "GICC_HPPIR";
                gicc.hppir
            }
            (0x001C..0x0020) => {
                // GICC_ABPR b RW 0x0000000xa Aliased Binary Point Register
                field = "GICC_ABPR";
                gicc.abpr
            }
            (0x0020..0x0024) => {
                // GICC_AIAR RO 0x000003FF Aliased Interrupt Acknowledge Register
                field = "GICC_AIAR";
                gicc.aiar
            }
            (0x0024..0x0028) => {
                // GICC_AEOIR WO - Aliased End of Interrupt Register
                field = "GICC_AEOIR";
                0
            }
            (0x0028..0x002c) => {
                // GICC_AHPPIR RO 0x000003FF Aliased Highest Priority Pending Interrupt Register
                field = "GICC_AHPPIR";
                gicc.ahppir
            }
            (0x002C..0x0040) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0x0040..0x00D0) => {
                // IMPLEMENTATION DEFINED registers
                field = "IMPLEMENTATION DEFINED registers";
                0
            }
            (0x00D0..0x00E0) => {
                // GICC_APR RW 0x00000000 Active Priorities Registers
                field = "GICC_APR";
                // TODO
                0
            }
            (0x00E0..0x00ED) => {
                // GICC_NSAPR RW 0x00000000 Non-secure Active Priorities Registers
                field = "GICC_NSAPR";
                // TODO
                0
            }
            (0x00ED..0x00FC) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0x00FC..0x0100) => {
                // GICC_IIDR RO IMPLEMENTATION DEFINED CPU Interface Identification Register
                field = "GICC_IIDR";
                gicc.iidr
            }
            (0x1000..0x1004) => {
                // GICC_DIR WO - Deactivate Interrupt Register
                field = "GICC_DIR";
                gicc.dir
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
                0
            }
        }
        .into();

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            kind = "CPU interface read",
            offset = ?tracing::Hex(offset),
            ?width,
            field,
            value = ?tracing::BinaryHex(value)
        );

        value
    }

    fn write(&self, offset: u64, value: u64, width: Width) {
        // [ref:TODO]: return Error
        assert_eq!(width, Width::_32);
        let value = value as u32;

        let gicc = &mut self.registers.lock().unwrap().1;
        let field: &'static str;
        match offset {
            (0x0000..0x0004) => {
                // GICC_CTLR RW 0x00000000 CPU Interface Control Register
                field = "GICC_CTLR";
                gicc.ctlr = value;
            }
            (0x0004..0x0008) => {
                // GICC_PMR RW 0x00000000 Interrupt Priority Mask Register
                field = "GICC_PMR";
                gicc.pmr = value;
            }
            (0x0008..0x000c) => {
                // GICC_BPR RW 0x0000000x a Binary Point Register
                field = "GICC_BPR";
                gicc.bpr = value;
            }
            (0x000C..0x0010) => {
                // GICC_IAR RO 0x000003FF Interrupt Acknowledge Register
                field = "GICC_IAR";
            }
            (0x0010..0x0014) => {
                // GICC_EOIR WO - End of Interrupt Register
                field = "GICC_EOIR";
                gicc.eoir = value;
            }
            (0x0014..0x0018) => {
                // GICC_RPR RO 0x000000FF Running Priority Register
                field = "GICC_RPR";
            }
            (0x0018..0x001c) => {
                // GICC_HPPIR RO 0x000003FF Highest Priority Pending Interrupt Register
                field = "GICC_HPPIR";
            }
            (0x001C..0x0020) => {
                // GICC_ABPR b RW 0x0000000xa Aliased Binary Point Register
                field = "GICC_ABPR";
                gicc.abpr = value;
            }
            (0x0020..0x0024) => {
                // GICC_AIAR RO 0x000003FF Aliased Interrupt Acknowledge Register
                field = "GICC_AIAR";
            }
            (0x0024..0x0028) => {
                // GICC_AEOIR WO - Aliased End of Interrupt Register
                field = "GICC_AEOIR";
                gicc.aeoir = value;
            }
            (0x0028..0x002c) => {
                // GICC_AHPPIR RO 0x000003FF Aliased Highest Priority Pending Interrupt Register
                field = "GICC_AHPPIR";
            }
            (0x002C..0x0040) => {
                field = "Reserved";
            }
            (0x0040..0x00D0) => {
                field = "IMPLEMENTATION DEFINED registers";
            }
            (0x00D0..0x00E0) => {
                // GICC_APR RW 0x00000000 Active Priorities Registers
                field = "GICC_APR";
                // TODO
            }
            (0x00E0..0x00ED) => {
                // GICC_NSAPR RW 0x00000000 Non-secure Active Priorities Registers
                field = "GICC_NSAPR";
                // TODO
            }
            (0x00ED..0x00FC) => {
                field = "Reserved";
            }
            (0x00FC..0x0100) => {
                // GICC_IIDR RO IMPLEMENTATION DEFINED CPU Interface Identification Register
                field = "GICC_IIDR";
            }
            (0x1000..0x1004) => {
                // GICC_DIR WO - Deactivate Interrupt Register
                field = "GICC_DIR";
                gicc.dir = value;
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
            }
        }

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            kind = "CPU interface write",
            offset = ?tracing::Hex(offset),
            ?width,
            field,
            value = ?tracing::BinaryHex(value),
        );
    }
}

#[derive(Debug)]
pub struct Gicd {
    /// Distributor Control Register
    pub ctlr: u32,
    /// Interrupt Controller Type Register
    pub typer: u32,
    /// Distributor Implementer Identification Register.
    pub iidr: u32,
    _reserved_0: [u32; 0x1D],
    /// Interrupt Group Registers
    pub igroupr: [u32; 0x20],
    /// Interrupt Set-Enable Registers.
    pub isenabler: [u32; 0x20],
    /// Interrupt Clear-Enable Registers.
    pub icenabler: [u32; 0x20],
    /// Interrupt Set-Pending Registers.
    pub ispendr: [u32; 0x20],
    /// Interrupt Clear-Pending Registers.
    pub icpendr: [u32; 0x20],
    /// Interrupt Set-Active Registers.
    pub isactiver: [u32; 0x20],
    /// Interrupt Clear-Active Registers.
    pub icactiver: [u32; 0x20],
    /// Interrupt Priority Registers.
    pub ipriorityr: [u32; 0x100],
    /// Interrupt Processor Targets Registers.
    pub itargetsr: [u32; 0x100],
    /// Interrupt Configuration Registers.
    pub icfgr: [u32; 0x40],
    _reserved_1: [u32; 0x80],
    /// Software Generated Interrupt Register.
    pub sgir: u32,
}

impl Gicd {
    pub const fn new() -> Self {
        Self {
            ctlr: 0,
            typer: 0b11111,
            iidr: 0,
            _reserved_0: [0; 0x1D],
            igroupr: [0; 0x20],
            isenabler: [0; 0x20],
            icenabler: [0; 0x20],
            ispendr: [0; 0x20],
            icpendr: [0; 0x20],
            isactiver: [0; 0x20],
            icactiver: [0; 0x20],
            ipriorityr: [0; 0x100],
            itargetsr: [0; 0x100],
            icfgr: [0; 0x40],
            _reserved_1: [0; 0x80],
            sgir: 0,
        }
    }
}

impl Default for Gicd {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Gicc {
    /// CPU Interface Control Register.
    pub ctlr: u32,
    /// Interrupt Priority Mask Register.
    pub pmr: u32,
    /// Binary Point Register.
    pub bpr: u32,
    /// Interrupt Acknowledge Register.
    pub iar: u32,
    /// End of Interrupt Register.
    pub eoir: u32,
    /// Running Priority Register.
    pub rpr: u32,
    /// Highest Priority Pending Interrupt Register.
    pub hppir: u32,
    /// Aliased Binary Point Register
    pub abpr: u32,
    /// Aliased Interrupt Acknowledge Register
    pub aiar: u32,
    /// Aliased End of Interrupt Register
    pub aeoir: u32,
    /// Aliased Highest Priority Pending Interrupt Register
    pub ahppir: u32,
    _reserved_0: [u32; 0x34],
    /// CPU Interface Identification Register.
    pub iidr: u32,
    _reserved_1: [u32; 0x3C0],
    /// Deactivate Interrupt Register.
    pub dir: u32,
}

impl Gicc {
    pub const fn new() -> Self {
        const MIN_BINARY_POINT: u32 = 0x3;

        Self {
            ctlr: 0,
            pmr: 0,
            bpr: MIN_BINARY_POINT,
            iar: 0x000003ff,
            eoir: 0,
            rpr: 0x000000ff,
            hppir: 0x000003ff,
            abpr: MIN_BINARY_POINT + 1,
            aiar: 0x000003ff,
            aeoir: 0,
            ahppir: 0x000003ff,
            _reserved_0: [0; 0x34],
            iidr: 0x2 << 16,
            _reserved_1: [0; 0x3C0],
            dir: 0,
        }
    }
}

impl Default for Gicc {
    fn default() -> Self {
        Self::new()
    }
}
