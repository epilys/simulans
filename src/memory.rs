// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Virtual machine memory types.

pub mod mmu;

mod map;
mod region;
mod tlb;

mod address;
mod size;

pub use address::*;
pub use map::*;
pub use region::*;
pub use size::*;
pub use tlb::TLB;

/// Default guest physical address to load kernel code to.
pub const KERNEL_ADDRESS: usize = 0x40080000;

/// Default starting offset of DRAM inside the physical address space.
pub const PHYS_MEM_START: u64 = 0x4000_0000;

#[derive(Clone, Copy, Eq, PartialEq, PartialOrd)]
#[repr(i32)]
/// Register/memory width in bits.
pub enum Width {
    /// 128-bit.
    _128 = 128,
    /// 64-bit.
    _64 = 64,
    /// 32-bit.
    _32 = 32,
    /// 16-bit.
    _16 = 16,
    /// 8-bit.
    _8 = 8,
}

impl std::fmt::Debug for Width {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::_8 => {
                write!(fmt, "8bit")
            }
            Self::_16 => {
                write!(fmt, "16bit")
            }
            Self::_32 => {
                write!(fmt, "32bit")
            }
            Self::_64 => {
                write!(fmt, "64bit")
            }
            Self::_128 => {
                write!(fmt, "128bit")
            }
        }
    }
}

impl From<Width> for cranelift::prelude::Type {
    fn from(width: Width) -> Self {
        use cranelift::codegen::ir::types::{I128, I16, I32, I64, I8};

        match width {
            Width::_8 => I8,
            Width::_16 => I16,
            Width::_32 => I32,
            Width::_64 => I64,
            Width::_128 => I128,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AccessType {
    /// Instruction FETCH
    IFETCH,
    /// Software load/store to a General Purpose Register
    GPR,
    /// Software ASIMD extension load/store instructions
    ASIMD,
    /// Software SVE load/store instructions
    SVE,
    /// Software SME load/store instructions
    SME,
    /// Sysop IC
    IC,
    /// Sysop DC (not DC {Z,G,GZ}VA)
    DC,
    /// Sysop DC {Z,G,GZ}VA
    DCZero,
    /// Sysop AT
    AT,
    /// NV2 memory redirected access
    NV2,
    /// Statistical Profiling buffer access
    SPE,
    /// Guarded Control Stack access
    GCS,
    /// Trace Buffer access
    TRBE,
    /// Granule Protection Table Walk
    GPTW,
    /// Access to the HACDBS structure
    HACDBS,
    /// Access to entries in HDBSS
    HDBSS,
    /// Translation Table Walk
    TTW,
}
