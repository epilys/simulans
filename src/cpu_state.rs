// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Execution state of an emulated CPU or Processing Element (PE), in Arm terms.

#![allow(non_snake_case)]

use std::sync::{Arc, Mutex};

use crate::memory::Address;

mod sysregs;
pub use sysregs::*;

mod memory;
pub use memory::*;

mod pstate;
pub use pstate::*;

mod exclusive_monitor;
pub use exclusive_monitor::*;

/// Regular registers.
#[derive(Debug)]
#[repr(C)]
#[allow(missing_docs)]
pub struct RegisterFile {
    pub x0: u64,
    pub x1: u64,
    pub x2: u64,
    pub x3: u64,
    pub x4: u64,
    pub x5: u64,
    pub x6: u64,
    pub x7: u64,
    pub x8: u64,
    pub x9: u64,
    pub x10: u64,
    pub x11: u64,
    pub x12: u64,
    pub x13: u64,
    pub x14: u64,
    pub x15: u64,
    pub x16: u64,
    pub x17: u64,
    pub x18: u64,
    pub x19: u64,
    pub x20: u64,
    pub x21: u64,
    pub x22: u64,
    pub x23: u64,
    pub x24: u64,
    pub x25: u64,
    pub x26: u64,
    pub x27: u64,
    pub x28: u64,
    pub x29: u64,
    // Link Register can be referred to as LR
    pub x30: u64,
    pub sp_el0: u64,
    pub sp_el1: u64,
    pub sp_el2: u64,
    pub sp_el3: u64,
    pub spsr_el1: u64,
    pub spsr_el2: u64,
    pub spsr_el3: u64,
    pub pstate: u64,
}

impl Default for RegisterFile {
    fn default() -> Self {
        Self {
            x0: 0,
            x1: 0,
            x2: 0,
            x3: 0,
            x4: 0,
            x5: 0,
            x6: 0,
            x7: 0,
            x8: 0,
            x9: 0,
            x10: 0,
            x11: 0,
            x12: 0,
            x13: 0,
            x14: 0,
            x15: 0,
            x16: 0,
            x17: 0,
            x18: 0,
            x19: 0,
            x20: 0,
            x21: 0,
            x22: 0,
            x23: 0,
            x24: 0,
            x25: 0,
            x26: 0,
            x27: 0,
            x28: 0,
            x29: 0,
            x30: 0,
            sp_el0: 0,
            sp_el1: 0,
            sp_el2: 0,
            sp_el3: 0,
            spsr_el1: 0,
            spsr_el2: 0,
            spsr_el3: 0,
            pstate: PSTATE::default().into(),
        }
    }
}

/// Classes of exception.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Exception {
    /// Uncategorized or unknown reason
    Uncategorized,
    /// Trapped WFI or WFE instruction
    WFxTrap,
    // /// Trapped AArch32 MCR or MRC access, coproc=0b111
    // CP15RTTrap,
    // /// Trapped AArch32 MCRR or MRRC access, coproc=0b1111
    // CP15RRTTrap,
    // /// Trapped AArch32 MCR or MRC access, coproc=0b1110
    // CP14RTTrap,
    // /// Trapped AArch32 LDC or STC access, coproc=0b1110
    // CP14DTTrap,
    // // Trapped AArch32 MRRC access, coproc=0b1110
    // CP14RRTTrap,
    /// HCPTR-trapped access to SIMD or FP
    //AdvSIMDFPAccessTrap,
    /// Trapped access to SIMD or FP ID register
    //FPIDTrap,
    /// Trapped access to ST64BV, ST64BV0, ST64B and LD64B
    //LDST64BTrap,
    // Trapped BXJ instruction not supported in Armv8
    /// Trapped invalid PAC use
    //PACTrap,
    /// Illegal Execution state
    IllegalState,
    /// Supervisor Call
    SupervisorCall,
    /// Hypervisor Call
    HypervisorCall,
    /// Monitor Call or Trapped SMC instruction
    MonitorCall,
    /// Trapped MRS or MSR System register access
    SystemRegisterTrap,
    /// Trapped invalid ERET use
    ERetTrap,
    /// Instruction Abort or Prefetch Abort
    InstructionAbort,
    /// PC alignment fault
    PCAlignment,
    /// Data Abort
    DataAbort,
    /// Data abort at EL1 reported as being from EL2
    NV2DataAbort,
    /// PAC Authentication failure
    PACFail,
    /// SP alignment fault
    SPAlignment,
    /// IEEE trapped FP exception
    FPTrappedException,
    /// `SError` interrupt
    SError,
    /// (Hardware) Breakpoint
    Breakpoint,
    /// Software Step
    SoftwareStep,
    /// Watchpoint
    Watchpoint,
    /// Watchpoint at EL1 reported as being from EL2
    NV2Watchpoint,
    /// Software Breakpoint Instruction
    SoftwareBreakpoint,
    // /// AArch32 Vector Catch
    // VectorCatch,
    /// IRQ interrupt
    IRQ,
    // // HCPTR trapped access to SVE
    // SVEAccessTrap,
    // // HCPTR trapped access to SME
    // SMEAccessTrap,
    // // Trapped TSTART access
    // TSTARTAccessTrap,
    // // Granule protection check
    // GPC,
    // // Branch Target Identification
    // BranchTarget,
    // // Exception from a CPY* or SET* instruction
    // MemCpyMemSet,
    // // GCS Exceptions
    // GCSFail,
    // // Profiling exception
    // Profiling,
    // // Trapped MRRS or MSRR System register or SYSP access
    // SystemRegister128Trap,
    /// FIQ interrupt
    FIQ,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// Numeric exit request ID that can be set from JIT code
#[repr(u8)]
pub enum ExitRequestID {
    /// Shut down the machine
    Poweroff = 0,
    WaitForInterrupt,
    Yield,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// Exit request to be serviced on main execution loop
pub enum ExitRequest {
    /// Shut down the machine
    Poweroff,
    WaitForInterrupt,
    Yield,
    /// Instruction or data abort
    Abort {
        /// Causing fault
        fault: crate::exceptions::FaultRecord,
        /// Return address
        preferred_exception_return: Address,
    },
}

impl From<ExitRequestID> for ExitRequest {
    fn from(id: ExitRequestID) -> Self {
        use ExitRequestID as Id;

        match id {
            Id::Poweroff => Self::Poweroff,
            Id::WaitForInterrupt => Self::WaitForInterrupt,
            Id::Yield => Self::Yield,
        }
    }
}

/// ID registers
#[derive(Debug)]
#[repr(C)]
pub struct IDRegisterFile {
    /// Main ID Register
    pub midr_el1: u64,
    /// `AArch64` Processor Feature Register 0
    pub id_aa64pfr0_el1: u64,
    /// `AArch64` Processor Feature Register 1
    pub id_aa64pfr1_el1: u64,
    /// `AArch64` Memory Model Feature Register 0
    pub id_aa64mmfr0_el1: u64,
    /// `AArch64` Memory Model Feature Register 1
    pub id_aa64mmfr1_el1: u64,
    /// `AArch64` Memory Model Feature Register 2
    pub id_aa64mmfr2_el1: u64,
    /// `AArch64` Memory Model Feature Register 3
    pub id_aa64mmfr3_el1: u64,
    /// `AArch64` Memory Model Feature Register 4
    pub id_aa64mmfr4_el1: u64,
    /// `AArch64` Instruction Set Attribute Register 0
    pub id_aa64isar0_el1: u64,
    /// Data Cache Zero ID Register
    pub dczid_el0: u64,
}

impl Default for IDRegisterFile {
    fn default() -> Self {
        let id_aa64pfr0_el1 = {
            const EL0: u64 = 1;
            const EL1: u64 = 1;
            const EL2: u64 = 0;
            const EL3: u64 = 0;
            const FP: u64 = 0b1111;
            const ADVSIMD: u64 = 0b1111;
            const GIC: u64 = 0;
            const SVE: u64 = 0;
            EL0 | EL1 << 4 | EL2 << 8 | EL3 << 12 | FP << 16 | ADVSIMD << 20 | GIC << 24 | SVE << 32
        };

        let id_aa64isar0_el1 = {
            const AES: u64 = false as u64;
            const SHA1: u64 = false as u64;
            const SHA2: u64 = false as u64;
            const CRC32: u64 = true as u64;
            // [ref:atomics]
            const ATOMIC: u64 = false as u64;
            const TME: u64 = false as u64;
            const RDM: u64 = false as u64;
            const SHA3: u64 = false as u64;
            const SM3: u64 = false as u64;
            const SM4: u64 = false as u64;
            const DP: u64 = false as u64;
            const FHM: u64 = false as u64;
            const TS: u64 = false as u64;
            const TLB: u64 = false as u64;
            const RNDR: u64 = true as u64;
            RNDR << 60
                | TLB << 56
                | TS << 52
                | FHM << 48
                | DP << 44
                | SM4 << 40
                | SM3 << 36
                | SHA3 << 32
                | RDM << 28
                | TME << 24
                | ATOMIC << 20
                | CRC32 << 16
                | SHA2 << 12
                | SHA1 << 8
                | AES << 4
        };
        let dczid_el0 = 0b100;
        Self {
            midr_el1: (0b1111) << 16,
            // vpidr_el2: (0b1111) << 16,
            id_aa64pfr0_el1,
            id_aa64pfr1_el1: 0,
            id_aa64mmfr0_el1: PARange::_1 as u64,
            id_aa64mmfr1_el1: 0,
            id_aa64mmfr2_el1: 0,
            id_aa64mmfr3_el1: 0,
            id_aa64mmfr4_el1: 0,
            id_aa64isar0_el1,
            dczid_el0,
        }
    }
}

#[derive(Copy, Clone, Debug)]
#[repr(u8)]
pub enum PARange {
    ///4GB 32 bits, `PA[31:0]`
    _1 = 0b0000,
    /// 64GB 36 bits, `PA[35:0]`
    _2 = 0b0001,
    ///1TB 40 bits, `PA[39:0]`
    _3 = 0b0010,
    /// 4TB 42 bits, `PA[41:0]`
    _4 = 0b0011,
    /// 16TB 44 bits, `PA[43:0]`
    _5 = 0b0100,
    /// 256TB 48 bits, `PA[47:0]`
    _6 = 0b0101,
    /// 4PB 52 bits, `PA[51:0]`
    _7 = 0b0110,
    /// 64PB 56 bits, `PA[55:0]`
    _8 = 0b0111,
}

impl IDRegisterFile {
    /// Returns `ID_AA64MMFR0_EL1.PARange` value.
    pub const fn pa_range(&self) -> PARange {
        match self.id_aa64mmfr0_el1 & 0b1111 {
            0b0000 => PARange::_1,
            0b0001 => PARange::_2,
            0b0010 => PARange::_3,
            0b0011 => PARange::_4,
            0b0100 => PARange::_5,
            0b0101 => PARange::_6,
            0b0110 => PARange::_7,
            0b0111 => PARange::_8,
            _other => unreachable!(),
        }
    }
}

/// Exception handling registers
#[derive(Default, Debug)]
#[repr(C)]
pub struct ExceptionRegisterFile {
    /// Exception return register, EL1
    pub elr_el1: u64,
    /// Exception return register, EL2
    pub elr_el2: u64,
    /// Exception return register, EL3
    pub elr_el3: u64,
    /// Auxiliary Fault Status Register 0, EL1, EL2, and EL3 (32-bit)
    pub afsr0_el1: u64,
    /// Auxiliary Fault Status Register 1, EL1, EL2, and EL3 (32-bit)
    pub afsr1_el1: u64,
    /// Exception Syndrome Register, EL1 (32-bit)
    pub esr_el1: u64,
    /// Instruction Fault Status Register, EL2 (32-bit)
    pub ifsr32_el2: u64,
    /// Auxiliary Fault Status Register 0, EL1, EL2, and EL3 (32-bit)
    pub afsr0_el2: u64,
    /// Auxiliary Fault Status Register 1, EL1, EL2, and EL3 (32-bit)
    pub afsr1_el2: u64,
    /// Exception Syndrome Register, EL2 (32-bit)
    pub esr_el2: u64,
    /// Auxiliary Fault Status Register 0, EL1, EL2, and EL3 (32-bit)
    pub afsr0_el3: u64,
    /// Auxiliary Fault Status Register 1, EL1, EL2, and EL3 (32-bit)
    pub afsr1_el3: u64,
    /// Exception Syndrome Register, EL3 (32-bit)
    pub esr_el3: u64,
    /// Fault Address Register, EL1
    pub far_el1: u64,
    /// Fault Address Register, EL2
    pub far_el2: u64,
    /// Hypervisor IPA Fault Address Register, EL2
    pub hpfar_el2: u64,
    /// Fault Address Register, EL3
    pub far_el3: u64,
    /// Vector Base Address Register, EL1
    pub vbar_el1: u64,
    /// Interrupt Status Register, EL1
    pub isr_el1: u64,
    /// Vector Base Address Register, EL2
    pub vbar_el2: u64,
    /// Vector Base Address Register, EL3
    pub vbar_el3: u64,
    /// Architectural Feature Trap Register (EL3)
    pub cptr_el3: u64,
}

/// Misc control registers.
#[derive(Default, Debug)]
#[repr(C)]
pub struct ControlRegisterFile {
    pub sctlr_el1: u64,
    pub sctlr_el2: u64,
    pub sctlr_el3: u64,
    pub cpacr_el1: u64,
    /// Hypervisor Configuration Register
    ///
    /// Controls virtualization settings and trapping of exceptions to EL2.
    pub hcr_el2: u64,
    /// Secure Configuration Register
    ///
    /// Controls Secure state and trapping of exceptions to EL3
    pub scr_el3: u64,
}

/// Timer registers.
#[derive(Debug, Default)]
#[repr(C)]
pub struct TimerRegisterFile {
    pub cntkctl_el1: u64,
}

/// All execution state of a processing element.
#[repr(C)]
#[derive(Default, Debug)]
pub struct ExecutionState {
    /// Local exclusive monitor
    pub monitor: ExclusiveMonitor,
    /// Regular registers.
    pub registers: RegisterFile,
    /// Vector (SIMD) registers.
    pub vector_registers: [u128; 32],
    /// ID registers.
    pub id_registers: IDRegisterFile,
    /// Timer registers.
    pub timer_registers: TimerRegisterFile,
    /// MMU registers.
    pub mmu_registers: MMURegisterFile,
    /// Exception handling registers
    pub exception_registers: ExceptionRegisterFile,
    /// Control registers
    pub control_registers: ControlRegisterFile,
    /// Exit request to be serviced on main execution loop.
    pub exit_request: Arc<Mutex<Option<ExitRequest>>>,
    /// Architectural features this CPU supports.
    pub arch_features: ArchFeatures,
}

impl ExecutionState {
    /// Whether `EL2` is enabled in this machine.
    pub const fn EL2_enabled(&self) -> bool {
        false
    }

    /// Whether `el` is supported in this machine.
    pub const fn have_el(&self, el: ExceptionLevel) -> bool {
        matches!(el, ExceptionLevel::EL0 | ExceptionLevel::EL1)
    }

    /// Returns `VBAR_ELx` register value depending on current exception level.
    pub fn vbar_elx(&self) -> u64 {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.exception_registers.vbar_el1,
            other => unimplemented!("other vbar for {other:?}"),
        }
    }

    /// Returns `ELR_ELx` register value depending on current exception level.
    pub fn elr_elx(&self) -> Address {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => Address(self.exception_registers.elr_el1),
            ExceptionLevel::EL2 => Address(self.exception_registers.elr_el2),
            ExceptionLevel::EL3 => Address(self.exception_registers.elr_el3),
        }
    }

    /// Sets `ELR_ELx` register value depending on current exception level.
    pub fn set_elr_elx(&mut self, val: u64) {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.exception_registers.elr_el1 = val,
            ExceptionLevel::EL2 => self.exception_registers.elr_el2 = val,
            ExceptionLevel::EL3 => self.exception_registers.elr_el3 = val,
        }
    }

    /// Sets `ESR_ELx` register value depending on target exception level.
    pub fn set_esr_elx(&mut self, val: u64, target_el: ExceptionLevel) {
        match target_el {
            ExceptionLevel::EL0 => unreachable!(),
            ExceptionLevel::EL1 => self.exception_registers.esr_el1 = val,
            ExceptionLevel::EL2 => self.exception_registers.esr_el2 = val,
            ExceptionLevel::EL3 => self.exception_registers.esr_el3 = val,
        }
    }

    /// Sets `FAR_ELx` register value depending on target exception level.
    pub fn set_far_elx(&mut self, val: u64, target_el: ExceptionLevel) {
        match target_el {
            ExceptionLevel::EL0 => unreachable!(),
            ExceptionLevel::EL1 => self.exception_registers.far_el1 = val,
            ExceptionLevel::EL2 => self.exception_registers.far_el2 = val,
            ExceptionLevel::EL3 => self.exception_registers.far_el3 = val,
        }
    }

    /// Returns `SCTLR_ELx` register value depending on current exception level.
    pub fn sctlr_elx(&self) -> u64 {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.control_registers.sctlr_el1,
            ExceptionLevel::EL2 => self.control_registers.sctlr_el2,
            ExceptionLevel::EL3 => self.control_registers.sctlr_el3,
        }
    }
}

bitflags::bitflags! {
    /// Bitflag of architectural features, currently does not affect emulation at all.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct ArchFeatures: u64 {
        /// Large System Extensions.
        const FEAT_LSE = 0b00000001;
    }
}

/// Default value is `FEAT_LSE`.
impl Default for ArchFeatures {
    fn default() -> Self {
        Self::FEAT_LSE
    }
}
