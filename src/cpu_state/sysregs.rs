// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

/// Helper struct to manage sysregs that bad64 doesn't support.
#[derive(Copy, Clone, Debug)]
pub struct SysRegEncoding {
    pub o0: u8,
    pub o1: u8,
    pub cm: u8,
    pub cn: u8,
    pub o2: u8,
}

#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub enum SysReg {
    /// `ID_AA64MMFR0_EL1`, `AArch64` Memory Model Feature Register 0
    ID_AA64MMFR0_EL1,
    /// `ID_AA64ISAR1_EL1`, `AArch64` Instruction Set Attribute Register 1
    ID_AA64ISAR1_EL1,
    /// `ID_AA64ISAR0_EL1`, `AArch64` Instruction Set Attribute Register 0
    ID_AA64ISAR0_EL1,
    /// `ID_AA64MMFR2_EL1`, `AArch64` Memory Model Feature Register 2
    ID_AA64MMFR2_EL1,
    /// `ID_AA64ISAR2_EL1`, `AArch64` Instruction Set Attribute Register 2
    ID_AA64ISAR2_EL1,
    /// `MIDR_EL1`
    MIDR_EL1,
    /// `MPIDR_EL1`, Multiprocessor Affinity Register
    MPIDR_EL1,
    /// `CTR_EL0`
    CTR_EL0,
    /// `CNTVCT_EL0`, Counter-timer Virtual Count Register
    CNTVCT_EL0,
    /// `ID_AA64PFR0_EL1` `AArch64` Processor Feature Register 0
    ID_AA64PFR0_EL1,
    /// `ID_AA64PFR1_EL1`, `AArch64` Processor Feature Register 1
    ID_AA64PFR1_EL1,
    /// `ID_AA64ZFR0_EL1`, SVE Feature ID Register 0
    ID_AA64ZFR0_EL1,
    /// `ID_AA64SMFR0_EL1`, SME Feature ID Register 0
    ID_AA64SMFR0_EL1,
    /// `GMID_EL1`, Multiple tag transfer ID Register
    GMID_EL1,
    /// [ref:TODO]: `ID_AA64DFR0_EL1` `AArch64` Debug Feature Register 0
    ID_AA64DFR0_EL1,
    /// `ID_AA64MMFR1_EL1`, `AArch64` Memory Model Feature Register 1
    ID_AA64MMFR1_EL1,
    /// `ID_AA64MMFR3_EL1`, `AArch64` Memory Model Feature Register 3
    ID_AA64MMFR3_EL1,
    /// `DCZID_EL0`, Data Cache Zero ID Register
    DCZID_EL0,
    /// `CLIDR_EL1`, Cache Level ID Register
    CLIDR_EL1,
    /// `REVIDR_EL1`, Revision ID Register
    REVIDR_EL1,
    /// `ID_AA64DFR1_EL1`, `AArch64` Debug Feature Register 1
    ID_AA64DFR1_EL1,
    /// `ID_DFR0_EL1`, `AArch32` Debug Feature Register 0
    ID_DFR0_EL1,
    /// `ID_DFR1_EL1`, `AArch32` Debug Feature Register 1
    ID_DFR1_EL1,
    /// `ID_ISAR0_EL1`
    ID_ISAR0_EL1,
    /// `ID_ISAR1_EL1`
    ID_ISAR1_EL1,
    /// `ID_ISAR2_EL1`
    ID_ISAR2_EL1,
    /// `ID_ISAR3_EL1` (RO)
    ID_ISAR3_EL1,
    /// `ID_ISAR4_EL1`,
    ID_ISAR4_EL1,
    /// `ID_ISAR5_EL1`,
    ID_ISAR5_EL1,
    /// `ID_ISAR6_EL1` (RO)
    ID_ISAR6_EL1,
    /// `ID_MMFR0_EL1` (RO)
    ID_MMFR0_EL1,
    /// `ID_MMFR1_EL1` (RO)
    ID_MMFR1_EL1,
    /// `ID_MMFR2_EL1` (RO)
    ID_MMFR2_EL1,
    /// `ID_MMFR3_EL1`, `AArch32` Memory Model Feature Register 3
    ID_MMFR3_EL1,
    /// `ID_MMFR4_EL1` (RO)
    ID_MMFR4_EL1,
    /// `ID_MMFR5_EL1`, `AArch32` Memory Model Feature Register 5
    ID_MMFR5_EL1,
    /// `ID_PFR0_EL1` (RO)
    ID_PFR0_EL1,
    /// `ID_PFR1_EL1` (RO)
    ID_PFR1_EL1,
    /// `ID_PFR2_EL1` (RO)
    ID_PFR2_EL1,
    /// `MVFR0_EL1` (RO)
    MVFR0_EL1,
    /// `MVFR1_EL1` (RO)
    MVFR1_EL1,
    /// `MVFR2_EL1` (RO)
    MVFR2_EL1,
    /// RNDRRS, Random Number Full Entropy
    RNDRRS,
    /// RNDR, Random Number
    RNDR,
    /// `TPIDR2_EL0`
    TPIDR2_EL0,
    /// `PIRE0_EL1`, Permission Indirection Register 0 (EL1)
    PIRE0_EL1,
    /// `PIR_EL1`, Permission Indirection Register 1 (EL1)
    PIR_EL1,
    /// `TCR2_EL1`, Extended Translation Control Register (EL1)
    TCR2_EL1,
    // [ref:pointer_auth]
    APDAKEYHI_EL1,
    APDAKEYLO_EL1,
    APDBKEYHI_EL1,
    APDBKEYLO_EL1,
    APIBKEYHI_EL1,
    APGAKEYHI_EL1,
    APGAKEYLO_EL1,
    APIAKEYHI_EL1,
    APIBKEYLO_EL1,
    APIAKEYLO_EL1,
    NZCV,
    DAIF,
    DAIFSet,
    DAIFClr,
    CurrentEL,
    SpSel,
    TCO,
    /// `PMUSERENR_EL0`, Performance Monitors User Enable Register
    PMUSERENR_EL0,
    /// `AMUSERENR_EL0`, Activity Monitors User Enable Register
    // (We don't implement FEAT_AMUv1)
    AMUSERENR_EL0,
    /// Monitor Debug System Control Register
    MDSCR_EL1,
    TCR_EL1,
    TTBR0_EL1,
    TTBR1_EL1,
    VTTBR_EL2,
    MAIR_EL1,
    AMAIR_EL1,
    TPIDR_EL0,
    TPIDRRO_EL0,
    TPIDR_EL1,
    CONTEXTIDR_EL1,
    ESR_EL1,
    ESR_EL2,
    ESR_EL3,
    VBAR_EL1,
    VBAR_EL2,
    VBAR_EL3,
    CPTR_EL3,
    ELR_EL1,
    ELR_EL2,
    ELR_EL3,
    SCTLR_EL1,
    SCTLR_EL2,
    SCTLR_EL3,
    CPACR_EL1,
    HCR_EL2,
    SCR_EL3,
    CNTFRQ_EL0,
    CNTKCTL_EL1,
    CNTV_CTL_EL0,
    CNTV_CVAL_EL0,
    CNTP_CTL_EL0,
    CNTP_CVAL_EL0,
    CNTP_TVAL_EL0,
    // Debugger locks, ignore
    OSLAR_EL1,
    // Debugger locks, ignore
    OSDLR_EL1,
    DBGBVR0_EL1,
    DBGBCR0_EL1,
    DBGBVR1_EL1,
    DBGBCR1_EL1,
    DBGBVR2_EL1,
    DBGBCR2_EL1,
    DBGBVR3_EL1,
    DBGBCR3_EL1,
    DBGBVR4_EL1,
    DBGBCR4_EL1,
    DBGBVR5_EL1,
    DBGBCR5_EL1,
    DBGWVR0_EL1,
    DBGWCR0_EL1,
    DBGWVR1_EL1,
    DBGWCR1_EL1,
    DBGWVR2_EL1,
    DBGWCR2_EL1,
    DBGWVR3_EL1,
    DBGWCR3_EL1,
    SP_EL0,
    SP_EL1,
    SP_EL2,
    SP_EL3,
    SPSR_EL1,
    SPSR_EL2,
    SPSR_EL3,
    FAR_EL1,
    FAR_EL2,
    FAR_EL3,
}

impl From<SysRegEncoding> for SysReg {
    fn from(reg: SysRegEncoding) -> Self {
        match reg {
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b111,
                o2: 0,
            } => Self::ID_AA64MMFR0_EL1,
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 7,
                o2: 2,
            } => Self::ID_AA64MMFR2_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b110,
                o2: 0,
            } => Self::ID_AA64ISAR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b110,
                o2: 0b1,
            } => Self::ID_AA64ISAR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b110,
                o2: 0b10,
            } => Self::ID_AA64ISAR2_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0,
                o2: 0,
            } => Self::MIDR_EL1,
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 0,
                o2: 5,
            } => Self::MPIDR_EL1,
            SysRegEncoding {
                o0: 3,
                o1: 3,
                cm: 0,
                cn: 0,
                o2: 1,
            } => Self::CTR_EL0,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b11,
                cm: 0b1110,
                cn: 0,
                o2: 0b10,
            } => Self::CNTVCT_EL0,
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 4,
                o2: 0,
            } => Self::ID_AA64PFR0_EL1,
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 4,
                o2: 1,
            } => Self::ID_AA64PFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b100,
                o2: 0b100,
            } => Self::ID_AA64ZFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b100,
                o2: 0b101,
            } => Self::ID_AA64SMFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b1,
                cm: 0,
                cn: 0,
                o2: 0b100,
            } => Self::GMID_EL1,
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 5,
                o2: 0,
            } => Self::ID_AA64DFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b111,
                o2: 1,
            } => Self::ID_AA64MMFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b111,
            } => Self::ID_MMFR3_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b110,
            } => Self::ID_MMFR4_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b110,
            } => Self::ID_MMFR5_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b000,
            } => Self::ID_PFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b001,
            } => Self::ID_PFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b100,
            } => Self::ID_PFR2_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b000,
            } => Self::MVFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b001,
            } => Self::MVFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b010,
            } => Self::MVFR2_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b111,
                o2: 0b11,
            } => Self::ID_AA64MMFR3_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b11,
                cm: 0,
                cn: 0,
                o2: 0b111,
            } => Self::DCZID_EL0,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b1,
                cm: 0,
                cn: 0,
                o2: 0b1,
            } => Self::CLIDR_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0,
                o2: 0b110,
            } => Self::REVIDR_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b101,
                o2: 0b1,
            } => Self::ID_AA64DFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b010,
            } => Self::ID_DFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b101,
            } => Self::ID_DFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b000,
            } => Self::ID_ISAR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b001,
            } => Self::ID_ISAR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b010,
            } => Self::ID_ISAR2_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b011,
            } => Self::ID_ISAR3_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b100,
            } => Self::ID_ISAR4_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b101,
            } => Self::ID_ISAR5_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0010,
                o2: 0b111,
            } => Self::ID_ISAR6_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b100,
            } => Self::ID_MMFR0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b101,
            } => Self::ID_MMFR1_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b110,
            } => Self::ID_MMFR2_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b0010,
                cn: 0b0100,
                o2: 0b001,
            } => Self::RNDRRS,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b0010,
                cn: 0b0100,
                o2: 0b000,
            } => Self::RNDR,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b1101,
                cn: 0b0000,
                o2: 0b101,
            } => Self::TPIDR2_EL0,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b1010,
                cn: 0b0010,
                o2: 0b010,
            } => Self::PIRE0_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b1010,
                cn: 0b0010,
                o2: 0b11,
            } => Self::PIR_EL1,
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0010,
                cn: 0b0000,
                o2: 0b011,
            } => Self::TCR2_EL1,
            _other => {
                unimplemented!("unimplemented sysreg encoding: {:?}", reg)
            }
        }
    }
}

impl From<&bad64::SysReg> for SysReg {
    fn from(reg: &bad64::SysReg) -> Self {
        match reg {
            bad64::SysReg::NZCV => Self::NZCV,
            bad64::SysReg::TCO => Self::TCO,
            bad64::SysReg::DAIFSET => Self::DAIFSet,
            bad64::SysReg::DAIFCLR => Self::DAIFClr,
            bad64::SysReg::CURRENTEL => Self::CurrentEL,
            bad64::SysReg::PSTATE_SPSEL => Self::SpSel,
            bad64::SysReg::PMUSERENR_EL0 => Self::PMUSERENR_EL0,
            bad64::SysReg::AMUSERENR_EL0 => Self::AMUSERENR_EL0,
            bad64::SysReg::MDSCR_EL1 => Self::MDSCR_EL1,
            bad64::SysReg::TCR_EL1 => Self::TCR_EL1,
            bad64::SysReg::TTBR0_EL1 => Self::TTBR0_EL1,
            bad64::SysReg::TTBR1_EL1 => Self::TTBR1_EL1,
            bad64::SysReg::VTTBR_EL2 => Self::VTTBR_EL2,
            bad64::SysReg::MAIR_EL1 => Self::MAIR_EL1,
            bad64::SysReg::AMAIR_EL1 => Self::AMAIR_EL1,
            bad64::SysReg::TPIDR_EL0 => Self::TPIDR_EL0,
            bad64::SysReg::TPIDRRO_EL0 => Self::TPIDRRO_EL0,
            bad64::SysReg::TPIDR_EL1 => Self::TPIDR_EL1,
            bad64::SysReg::CONTEXTIDR_EL1 => Self::CONTEXTIDR_EL1,
            bad64::SysReg::ESR_EL1 => Self::ESR_EL1,
            bad64::SysReg::ESR_EL2 => Self::ESR_EL2,
            bad64::SysReg::ESR_EL3 => Self::ESR_EL3,
            bad64::SysReg::FAR_EL1 => Self::FAR_EL1,
            bad64::SysReg::FAR_EL2 => Self::FAR_EL2,
            bad64::SysReg::FAR_EL3 => Self::FAR_EL3,
            bad64::SysReg::VBAR_EL1 => Self::VBAR_EL1,
            bad64::SysReg::VBAR_EL2 => Self::VBAR_EL2,
            bad64::SysReg::VBAR_EL3 => Self::VBAR_EL3,
            bad64::SysReg::CPTR_EL3 => Self::CPTR_EL3,
            bad64::SysReg::ELR_EL1 => Self::ELR_EL1,
            bad64::SysReg::ELR_EL2 => Self::ELR_EL2,
            bad64::SysReg::ELR_EL3 => Self::ELR_EL3,
            bad64::SysReg::SCTLR_EL1 => Self::SCTLR_EL1,
            bad64::SysReg::SCTLR_EL2 => Self::SCTLR_EL2,
            bad64::SysReg::SCTLR_EL3 => Self::SCTLR_EL3,
            bad64::SysReg::CPACR_EL1 => Self::CPACR_EL1,
            bad64::SysReg::HCR_EL2 => Self::HCR_EL2,
            bad64::SysReg::SCR_EL3 => Self::SCR_EL3,
            bad64::SysReg::CNTFRQ_EL0 => Self::CNTFRQ_EL0,
            bad64::SysReg::CNTKCTL_EL1 => Self::CNTKCTL_EL1,
            bad64::SysReg::CNTV_CTL_EL0 => Self::CNTV_CTL_EL0,
            bad64::SysReg::CNTV_CVAL_EL0 => Self::CNTV_CVAL_EL0,
            bad64::SysReg::CNTP_CTL_EL0 => Self::CNTP_CTL_EL0,
            bad64::SysReg::CNTP_CVAL_EL0 => Self::CNTP_CVAL_EL0,
            bad64::SysReg::CNTP_TVAL_EL0 => Self::CNTP_TVAL_EL0,
            bad64::SysReg::OSLAR_EL1 => Self::OSLAR_EL1,
            bad64::SysReg::OSDLR_EL1 => Self::OSDLR_EL1,
            bad64::SysReg::DBGBVR0_EL1 => Self::DBGBVR0_EL1,
            bad64::SysReg::DBGBCR0_EL1 => Self::DBGBCR0_EL1,
            bad64::SysReg::DBGBVR1_EL1 => Self::DBGBVR1_EL1,
            bad64::SysReg::DBGBCR1_EL1 => Self::DBGBCR1_EL1,
            bad64::SysReg::DBGBVR2_EL1 => Self::DBGBVR2_EL1,
            bad64::SysReg::DBGBCR2_EL1 => Self::DBGBCR2_EL1,
            bad64::SysReg::DBGBVR3_EL1 => Self::DBGBVR3_EL1,
            bad64::SysReg::DBGBCR3_EL1 => Self::DBGBCR3_EL1,
            bad64::SysReg::DBGBVR4_EL1 => Self::DBGBVR4_EL1,
            bad64::SysReg::DBGBCR4_EL1 => Self::DBGBCR4_EL1,
            bad64::SysReg::DBGBVR5_EL1 => Self::DBGBVR5_EL1,
            bad64::SysReg::DBGBCR5_EL1 => Self::DBGBCR5_EL1,
            bad64::SysReg::DBGWVR0_EL1 => Self::DBGWVR0_EL1,
            bad64::SysReg::DBGWCR0_EL1 => Self::DBGWCR0_EL1,
            bad64::SysReg::DBGWVR1_EL1 => Self::DBGWVR1_EL1,
            bad64::SysReg::DBGWCR1_EL1 => Self::DBGWCR1_EL1,
            bad64::SysReg::DBGWVR2_EL1 => Self::DBGWVR2_EL1,
            bad64::SysReg::DBGWCR2_EL1 => Self::DBGWCR2_EL1,
            bad64::SysReg::DBGWVR3_EL1 => Self::DBGWVR3_EL1,
            bad64::SysReg::DBGWCR3_EL1 => Self::DBGWCR3_EL1,
            bad64::SysReg::APDAKEYHI_EL1 => Self::APDAKEYHI_EL1,
            bad64::SysReg::APDAKEYLO_EL1 => Self::APDAKEYLO_EL1,
            bad64::SysReg::APDBKEYHI_EL1 => Self::APDBKEYHI_EL1,
            bad64::SysReg::APDBKEYLO_EL1 => Self::APDBKEYLO_EL1,
            bad64::SysReg::APIBKEYHI_EL1 => Self::APIBKEYHI_EL1,
            bad64::SysReg::APGAKEYHI_EL1 => Self::APGAKEYHI_EL1,
            bad64::SysReg::APGAKEYLO_EL1 => Self::APGAKEYLO_EL1,
            bad64::SysReg::APIAKEYHI_EL1 => Self::APIAKEYHI_EL1,
            bad64::SysReg::APIBKEYLO_EL1 => Self::APIBKEYLO_EL1,
            bad64::SysReg::APIAKEYLO_EL1 => Self::APIAKEYLO_EL1,
            bad64::SysReg::SP_EL0 => Self::SP_EL0,
            bad64::SysReg::SP_EL1 => Self::SP_EL1,
            bad64::SysReg::SP_EL2 => Self::SP_EL2,
            // bad64::SysReg::SP_EL3 => Self::SP_EL3,
            bad64::SysReg::SPSR_EL1 => Self::SPSR_EL1,
            bad64::SysReg::SPSR_EL2 => Self::SPSR_EL2,
            bad64::SysReg::SPSR_EL3 => Self::SPSR_EL3,
            _other => {
                unimplemented!("unimplemented sysreg: {:?}", reg)
            }
        }
    }
}
