// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Memory management unit types

use bilge::prelude::*;

use super::{ExceptionLevel, ExecutionState};

/// MMU registers
#[derive(Default, Debug)]
#[repr(C)]
pub struct MMURegisterFile {
    /// Permission Indirection Register 0 (EL1)
    pub pire0_el1: u64,
    /// Permission Indirection Register 1 (EL1)
    pub pir_el1: u64,
    /// Translation Control Register (EL1)
    pub tcr_el1: u64,
    /// Extended Translation Control Register (EL1)
    pub tcr2_el1: u64,
    /// EL1 Translation Table Base Register 0
    pub ttbr0_el1: u64,
    /// EL1 Translation Table Base Register 1
    pub ttbr1_el1: u64,
    pub ttbr0_el2: u64,
    pub ttbr1_el2: u64,
    pub ttbr0_el3: u64,
    /// Virtualization Translation Table Base Register.
    pub vttbr_el2: u64,
    /// EL1 Memory Attribute Indirection Register
    pub mair_el1: u64,
    // pub mair_el2: u64,
    // pub mair_el3: u64,
    pub mair2_el1: u64,
    /// Auxiliary Memory Attribute Indirection Register (EL1)
    ///
    /// Register contents are implementation defined and not assigned any
    /// meaning by the spec.
    pub amair_el1: u64,
    pub amair2_el1: u64,
    /// Context ID Register (EL1)
    pub contextidr_el1: u64,
    // TLS registers for guest software use
    /// User Read and Write Thread ID Register
    pub tpidr_el0: u64,
    /// EL0 Read/Write Software Thread ID Register 2
    pub tpidr2_el0: u64,
    /// User Read-Only Thread ID Register
    pub tpidrro_el0: u64,
    /// Thread ID Register, privileged accesses only
    pub tpidr_el1: u64,
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, FromBits, DebugBits)]
/// Translation Table Base Register `TTBRn_ELx`.
pub struct TranslationTableBaseRegister {
    pub _CnP: u1,
    pub BADDR: u47,
    pub ASID: u16,
}

#[derive(Debug, Copy, Clone)]
pub enum Granule {
    _16KB = 0b01,
    _4KB = 0b10,
    _64KB = 0b11,
}

impl Granule {
    /// Returns the number of least-significant address bits within a single
    /// Translation Granule.
    ///
    /// `TGBits()`
    pub fn bits(&self) -> u8 {
        match self {
            Self::_4KB => 12,
            Self::_16KB => 14,
            Self::_64KB => 16,
        }
    }
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, FromBits, DebugBits)]
pub struct TranslationControlRegister {
    /// `T0SZ[5:0]`
    pub T0SZ: u6,
    /// `_res_0[6:6]`
    pub _res_0: u1,
    /// `EPD0[7:7]`
    pub EPD0: u1,
    /// `IRGN0[9:8]`
    pub IRGN0: u2,
    /// `ORGN0[11:10]`
    pub ORGN0: u2,
    /// `SH0[13:12]`
    pub SH0: u2,
    /// `TG0[15:14]`
    pub TG0: u2,
    /// `T1SZ[21:16]`
    pub T1SZ: u6,
    /// `A1[22:22]`
    pub A1: bool,
    /// `EPD1[23:23]`
    pub EPD1: u1,
    /// `IRGN1[25:24]`
    pub IRGN1: u2,
    /// `ORGN1[27:26]`
    pub ORGN1: u2,
    /// `SH1[29:28]`
    pub SH1: u2,
    /// `TG1[31:30]`
    pub TG1: u2,
    /// `IPS[34:32]`
    pub IPS: u3,
    /// `_res_1[35:35]`
    pub _res_1: u1,
    /// `AS[36:36]`
    pub AS: u1,
    /// `TBI0[37:37]`
    pub TBI0: bool,
    /// `TBI1[38:38]`
    pub TBI1: bool,
    /// `HA[39:39]`
    pub HA: u1,
    /// `HD[40:40]`
    pub HD: u1,
    /// `HPD0[41:41]`
    pub HPD0: u1,
    /// `HPD1[42:42]`
    pub HPD1: u1,
    /// `HWU059[43:43]`
    pub HWU059: u1,
    /// `HWU060[44:44]`
    pub HWU060: u1,
    /// `HWU061[45:45]`
    pub HWU061: u1,
    /// `HWU062[46:46]`
    pub HWU062: u1,
    /// `HWU159[47:47]`
    pub HWU159: u1,
    /// `HWU160[48:48]`
    pub HWU160: u1,
    /// `HWU161[49:49]`
    pub HWU161: u1,
    /// `HWU162[50:50]`
    pub HWU162: u1,
    /// `TBID0[51:51]`
    pub TBID0: u1,
    /// `TBID1[52:52]`
    pub TBID1: u1,
    /// `NFD0[53:53]`
    pub NFD0: u1,
    /// `NFD1[54:54]`
    pub NFD1: u1,
    /// `E0PD0[55:55]`
    pub E0PD0: u1,
    /// `E0PD1[56:56]`
    pub E0PD1: u1,
    /// `TCMA0[57:57]`
    pub TCMA0: u1,
    /// `TCMA1[58:58]`
    pub TCMA1: u1,
    /// `DS[59:59]`
    pub DS: u1,
    /// `MTX0[60:60]`
    pub MTX0: u1,
    /// `MTX1[61:61]`
    pub MTX1: u1,
    /// `_res_2[63:62]`
    pub _res_2: u2,
}

impl TranslationControlRegister {
    pub fn ttbr0_granule(&self) -> Granule {
        // `AArch64.S1DecodeTG0`
        match u8::from(self.TG0()) {
            0b00 => Granule::_4KB,
            0b01 => Granule::_64KB,
            0b10 => Granule::_16KB,
            other => unreachable!("0b{other:b}"),
        }
    }

    pub fn ttbr1_granule(&self) -> Granule {
        // `AArch64.S1DecodeTG1`
        match u8::from(self.TG1()) {
            0b10 => Granule::_4KB,
            0b11 => Granule::_64KB,
            0b01 => Granule::_16KB,
            other => unreachable!("0b{other:b}"),
        }
    }
}

impl ExecutionState {
    /// Returns `TCR_ELx` register value depending on current exception level.
    pub fn tcr_elx(&self) -> u64 {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.mmu_registers.tcr_el1,
            ExceptionLevel::EL2 => unimplemented!(),
            ExceptionLevel::EL3 => unimplemented!(),
        }
    }
}
