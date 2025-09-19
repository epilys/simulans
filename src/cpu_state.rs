// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Execution state of an emulated CPU or Processing Element (PE), in Arm terms.

#![allow(non_snake_case)]

use codegen::ir::types::{I128, I64};
use cranelift::prelude::*;
use indexmap::IndexMap;
use num_traits::cast::FromPrimitive;

use crate::{machine::Armv8AMachine, memory::Address};

mod memory;
pub use memory::*;

mod pstate;
pub use pstate::*;

const TRUSTED_MEMFLAGS: MemFlags =
    MemFlags::trusted().with_endianness(codegen::ir::Endianness::Little);

/// Regular registers.
#[derive(Default, Debug)]
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
    /// Selected `SP` based on current Exception Level and PSTATE's [`SpSel`].
    pub sp: u64,
    pub sp_el0: u64,
    pub sp_el1: u64,
    pub sp_el2: u64,
    pub sp_el3: u64,
    pub spsr_el1: u64,
    pub spsr_el2: u64,
    pub spsr_el3: u64,
    pub pstate: u64,
}

/// Classes of exception.
#[derive(Copy, Clone, Debug)]
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

#[derive(Copy, Clone, Debug)]
/// Exit request to be serviced on main execution loop
pub enum ExitRequest {
    /// Instruction or data abort
    Abort {
        /// Causing fault
        fault: crate::exceptions::FaultRecord,
        /// Return address
        preferred_exception_return: Address,
    },
}

/// ID registers
#[derive(Debug)]
#[repr(C)]
pub struct IDRegisterFile {
    /// Main ID Register
    pub midr_el1: u64,
    /// `AArch64` Processor Feature Register 0
    pub id_aa64pfr0_el1: u64,
    /// `AArch64` Memory Model Feature Register 0
    pub id_aa64mmfr0_el1: u64,
    /// `AArch64` Memory Model Feature Register 1
    pub id_aa64mmfr1_el1: u64,
    /// `AArch64` Memory Model Feature Register 2
    pub id_aa64mmfr2_el1: u64,
    /// `AArch64` Memory Model Feature Register 3
    pub id_aa64mmfr3_el1: u64,
    /// Data Cache Zero ID Register
    pub dczid_el0: u64,
}

impl Default for IDRegisterFile {
    fn default() -> Self {
        let mut id_aa64pfr0_el1 = 0;
        // EL0, bits [3:0] EL0 Exception level handling.
        id_aa64pfr0_el1 = crate::set_bits!(id_aa64pfr0_el1, off = 0, len = 4, val = 0b0001); // EL0 can be executed in AArch64 state only.
                                                                                             // EL1, bits [7:4] EL1 Exception level handling.
        id_aa64pfr0_el1 = crate::set_bits!(id_aa64pfr0_el1, off = 4, len = 4, val = 0b0001); // EL1 can be executed in AArch64 state only.

        // EL2, bits [11:8] EL2 is not implemented.

        // EL3, bits [15:12] ditto.

        // FP, bits [19:16]
        id_aa64pfr0_el1 = crate::set_bits!(id_aa64pfr0_el1, off = 16, len = 4, val = 0b1111); // Floating-point is not implemented.

        // AdvSIMD, bits [23:20]
        id_aa64pfr0_el1 = crate::set_bits!(id_aa64pfr0_el1, off = 20, len = 4, val = 0b1111); // Advanced SIMD is not implemented.

        // GIC, bits [27:24]
        id_aa64pfr0_el1 = crate::set_bits!(id_aa64pfr0_el1, off = 24, len = 4, val = 0b0000); // No GIC

        let dczid_el0 = 0b1000;
        Self {
            midr_el1: (0b1111) << 16,
            // vpidr_el2: (0b1111) << 16,
            id_aa64pfr0_el1,
            id_aa64mmfr0_el1: PARange::_1 as u64,
            id_aa64mmfr1_el1: 0,
            id_aa64mmfr2_el1: 0,
            id_aa64mmfr3_el1: 0,
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

/// All execution state of a processing element.
#[repr(C)]
#[derive(Default, Debug)]
pub struct ExecutionState {
    /// Regular registers.
    pub registers: RegisterFile,
    /// Vector (SIMD) registers.
    pub vector_registers: [u128; 32],
    /// ID registers.
    pub id_registers: IDRegisterFile,
    /// MMU registers.
    pub mmu_registers: MMURegisterFile,
    /// Exception handling registers
    pub exception_registers: ExceptionRegisterFile,
    /// Control registers
    pub control_registers: ControlRegisterFile,
    /// Exit request to be serviced on main execution loop.
    pub exit_request: Option<ExitRequest>,
    /// Architectural features this CPU supports.
    pub arch_features: ArchFeatures,
}

impl ExecutionState {
    /// Generate JIT instructions to assign a variable for each register and set
    /// it with its value.
    ///
    /// Used as a preamble to a translation block.
    pub fn load_cpu_state(
        machine_ptr: Value,
        builder: &mut FunctionBuilder,
        registers: &mut IndexMap<bad64::Reg, Variable>,
        sys_registers: &mut IndexMap<bad64::SysReg, Variable>,
    ) {
        use bad64::{Reg, SysReg};

        macro_rules! reg_field {
            ($($field:ident$([$index:expr])? => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iadd_imm(machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field) $(+ $index * std::mem::size_of::<u128>())*;
                    let value = builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, i32::try_from(offset).unwrap());
                    assert!(!registers.contains_key(&$bad_reg));
                    let var = builder.declare_var(I64);
                    registers.insert($bad_reg, var);
                    builder.def_var(var, value);
                )*
            }};
            (sys $($field:ident => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iadd_imm(machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    let value = builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, i32::try_from(offset).unwrap());
                    assert!(!sys_registers.contains_key(&$bad_sys_reg));
                    let var = builder.declare_var(I64);
                    sys_registers.insert($bad_sys_reg, var);
                    builder.def_var(var, value);
                )*
            }};
        }
        reg_field! { sys
            sp_el0 => SysReg::SP_EL0,
            sp_el1 => SysReg::SP_EL1,
            sp_el2 => SysReg::SP_EL2,
            // [ref:FIXME]: bad64 doesn't have an SP_EL3 variant.
            // sp_el3 => SysReg::SP_EL3,
            spsr_el3 =>  SysReg::SPSR_EL3,
            spsr_el1 => SysReg::SPSR_EL1,
        }
        reg_field! {
            x0 => Reg::X0,
            x1 => Reg::X1,
            x2 => Reg::X2,
            x3 => Reg::X3,
            x4 => Reg::X4,
            x5 => Reg::X5,
            x6 => Reg::X6,
            x7 => Reg::X7,
            x8 => Reg::X8,
            x9 => Reg::X9,
            x10 => Reg::X10,
            x11 => Reg::X11,
            x12 => Reg::X12,
            x13 => Reg::X13,
            x14 => Reg::X14,
            x15 => Reg::X15,
            x16 => Reg::X16,
            x17 => Reg::X17,
            x18 => Reg::X18,
            x19 => Reg::X19,
            x20 => Reg::X20,
            x21 => Reg::X21,
            x22 => Reg::X22,
            x23 => Reg::X23,
            x24 => Reg::X24,
            x25 => Reg::X25,
            x26 => Reg::X26,
            x27 => Reg::X27,
            x28 => Reg::X28,
            x29 => Reg::X29,
            x30 => Reg::X30,
            sp => Reg::SP,
        }
        {
            let zero = builder.ins().iconst(I64, 0);
            debug_assert!(!registers.contains_key(&Reg::XZR));
            let var = builder.declare_var(I64);
            registers.insert(Reg::XZR, var);
            builder.def_var(var, zero);
        }
        let vector_addr = builder.ins().iadd_imm(
            machine_ptr,
            std::mem::offset_of!(Armv8AMachine, cpu_state.vector_registers) as i64,
        );
        for i in 0_u32..=31 {
            let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
            assert!(!registers.contains_key(&v_reg));
            let offset = i * std::mem::size_of::<u128>() as u32;
            let offset = i32::try_from(offset).unwrap();
            let v_value = builder
                .ins()
                .load(I128, TRUSTED_MEMFLAGS, vector_addr, offset as i32);
            let v_var = builder.declare_var(I128);
            registers.insert(v_reg, v_var);
            builder.def_var(v_var, v_value);
        }
    }

    /// Generate JIT instructions to store register values back to `self`.
    ///
    /// Used as an epilogue of a translation block.
    pub fn save_cpu_state(
        machine_ptr: Value,
        builder: &mut FunctionBuilder,
        registers: &IndexMap<bad64::Reg, Variable>,
        sys_registers: &IndexMap<bad64::SysReg, Variable>,
        write_to_sysreg: bool,
        write_to_simd: bool,
    ) {
        use bad64::{Reg, SysReg};

        macro_rules! reg_field {
            ($($field:ident$([$index:expr])? => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iadd_imm(machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field) $(+ $index * std::mem::size_of::<u128>())*;
                    assert!(registers.contains_key(&$bad_reg));
                    let var = &registers[&$bad_reg];
                    let var_value = builder.use_var(*var);
                    builder.ins().store(TRUSTED_MEMFLAGS, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
            (sys $($field:ident$($conversion:expr)? => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iadd_imm(machine_ptr, std::mem::offset_of!(Armv8AMachine, cpu_state.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    assert!(sys_registers.contains_key(&$bad_sys_reg));
                    let var = &sys_registers[&$bad_sys_reg];
                    let var_value = builder.use_var(*var);
                    builder.ins().store(TRUSTED_MEMFLAGS, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
        }

        if write_to_sysreg {
            reg_field! { sys
                sp_el0 => SysReg::SP_EL0,
                sp_el1 => SysReg::SP_EL1,
                sp_el2 => SysReg::SP_EL2,
                // sp_el3 => SysReg::SP_EL3,
                // [ref:FIXME]: bad64 doesn't have an SP_EL3 variant.
                spsr_el3 =>  SysReg::SPSR_EL3,
                spsr_el1 => SysReg::SPSR_EL1,
            };
        }
        reg_field! {
            x0 => Reg::X0,
            x1 => Reg::X1,
            x2 => Reg::X2,
            x3 => Reg::X3,
            x4 => Reg::X4,
            x5 => Reg::X5,
            x6 => Reg::X6,
            x7 => Reg::X7,
            x8 => Reg::X8,
            x9 => Reg::X9,
            x10 => Reg::X10,
            x11 => Reg::X11,
            x12 => Reg::X12,
            x13 => Reg::X13,
            x14 => Reg::X14,
            x15 => Reg::X15,
            x16 => Reg::X16,
            x17 => Reg::X17,
            x18 => Reg::X18,
            x19 => Reg::X19,
            x20 => Reg::X20,
            x21 => Reg::X21,
            x22 => Reg::X22,
            x23 => Reg::X23,
            x24 => Reg::X24,
            x25 => Reg::X25,
            x26 => Reg::X26,
            x27 => Reg::X27,
            x28 => Reg::X28,
            x29 => Reg::X29,
            x30 => Reg::X30,
            sp => Reg::SP,
        }
        if write_to_simd {
            let vector_addr = builder.ins().iadd_imm(
                machine_ptr,
                std::mem::offset_of!(Armv8AMachine, cpu_state.vector_registers) as i64,
            );
            for i in 0_u32..=31 {
                let offset = i * std::mem::size_of::<u128>() as u32;
                let offset = i32::try_from(offset).unwrap();
                let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
                assert!(registers.contains_key(&v_reg));
                let var = &registers[&v_reg];
                let value = builder.use_var(*var);
                builder
                    .ins()
                    .store(TRUSTED_MEMFLAGS, value, vector_addr, offset);
            }
        }
    }

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
