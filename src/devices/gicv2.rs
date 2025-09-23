// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! # ARM ® Generic Interrupt Controller Architecture version 2.0

use std::sync::{Arc, Mutex};

use crate::{memory::Width, tracing};

#[derive(Debug)]
pub struct GicV2 {
    /// Device ID.
    pub device_id: u64,
    pub registers: Arc<Mutex<(Gicd, Gicc)>>,
}

impl GicV2 {
    pub fn new(device_id: u64) -> Self {
        Self {
            device_id,
            registers: Arc::new(Mutex::new((
                Gicd {
                    ctlr: 0,
                    typer: 0,
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
                },
                Gicc {
                    ctlr: 0,
                    pmr: 0,
                    bpr: 0,
                    iar: 0,
                    eoir: 0,
                    rpr: 0,
                    hppir: 0,
                    abpr: 0,
                    aiar: 0,
                    aeoir: 0,
                    ahppir: 0,
                    _reserved_0: [0; 0x34],
                    iidr: 0,
                    _reserved_1: [0; 0x3C0],
                    dir: 0,
                },
            ))),
        }
    }
}

impl crate::devices::Device for GicV2 {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn ops(&self) -> Box<dyn crate::memory::DeviceMemoryOps> {
        Box::new(GicV2MemoryOps {
            device_id: self.device_id,
            registers: self.registers.clone(),
        })
    }
}

#[derive(Debug)]
struct GicV2MemoryOps {
    device_id: u64,
    #[allow(dead_code)]
    registers: Arc<Mutex<(Gicd, Gicc)>>,
}

impl crate::memory::DeviceMemoryOps for GicV2MemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> u64 {
        tracing::event!(
            target: tracing::TraceItem::Pl011.as_str(),
            tracing::Level::TRACE,
            kind = "read",
            offset = ?tracing::Hex(offset),
            ?width,
        );
        17
    }

    fn write(&self, offset: u64, value: u64, width: Width) {
        tracing::event!(
            target: tracing::TraceItem::Pl011.as_str(),
            tracing::Level::TRACE,
            kind = "write",
            offset = ?tracing::Hex(offset),
            ?width,
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
