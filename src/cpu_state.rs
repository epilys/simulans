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

//! Execution state of an emulated CPU or Processing Element (PE), in Arm terms.

#![allow(non_snake_case)]

use bilge::prelude::*;
use codegen::ir::types::I64;
use cranelift::prelude::*;
use indexmap::IndexMap;
use num_traits::cast::FromPrimitive;

pub extern "C" fn print_registers(machine: &crate::machine::Armv8AMachine, is_entry: bool) {
    if is_entry {
        tracing::event!(
            target: "block_entry",
            tracing::Level::TRACE,
            "entering block pc = 0x{:x}, prev_pc = 0x{:x} with registers:\n{:#?}",
            machine.pc,
            machine.prev_pc,
            machine.cpu_state.registers
        );
    } else {
        tracing::event!(
            target: "block_exit",
            tracing::Level::TRACE,
            "exiting block from 0x{:x} to pc 0x{:x} with registers:\n{:#?}",
            machine.prev_pc,
            machine.pc,
            machine.cpu_state.registers
        );
    }
}

/// Regular registers.
#[derive(Default, Debug)]
#[repr(C)]
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
    pub xzr: u64,
    /// Selected `SP` based on current Exception Level and PSTATE's [`SpSel`].
    pub sp: u64,
    pub sp_el0: u64,
    pub sp_el1: u64,
    pub sp_el2: u64,
    pub sp_el3: u64,
    // Translation Table Base Register 0: Holds the base address of translation table 0, and
    // information about the memory it occupies. This is one of the translation tables for the
    // stage 1 translation of memory accesses at ELn.
    /// EL1 Translation Table Base Register 0
    pub ttbr0_el1: u64,
    // pub ttbr0_el2: u64,
    // pub ttbr0_el3: u64,
    pub vttbr_el2: u64,
    // Memory Attribute Indirection Register: Provides the memory attribute encodings corresponding
    // to the possible values in a Long- descriptor format translation table entry for stage 1
    // translations at ELn.
    /// EL1 Memory Attribute Indirection Register
    pub mair_el1: u64,
    // pub mair_el2: u64,
    // pub mair_el3: u64,
    pub vpidr_el2: u64,
    pub vmpidr_el2: u64,
    pub id_aa64mmfr0_el1: u64,
    pub tcr_el1: u64,
    pub sctlr_el1: u64,
    pub sctlr_el2: u64,
    pub sctlr_el3: u64,
    pub cpacr_el1: u64,
    // Vector Based Address Register Holds the exception base address for any exception that is
    // taken to ELn.
    /// EL1 Vector Based Address Register
    pub vbar_el1: u64,
    // pub vbar_el2: u64,
    // pub vbar_el3: u64,
    /// Hypervisor Configuration Register
    ///
    /// Controls virtualization settings and trapping of exceptions to EL2.
    pub hcr_el2: u64,
    /// Secure Configuration Register
    ///
    /// Controls Secure state and trapping of exceptions to EL3
    pub scr_el3: u64,
    pub spsr_el1: SavedProgramStatusRegister,
    pub spsr_el2: SavedProgramStatusRegister,
    pub spsr_el3: SavedProgramStatusRegister,
    pub elr_el1: u64,
    pub elr_el2: u64,
    pub elr_el3: u64,
    pub esr_el1: u64,
    pub nzcv: NZCV,
}

#[bitsize(2)]
#[derive(Copy, Clone, Default, FromBits, Debug, Eq, PartialEq)]
/// Exception level
pub enum ExceptionLevel {
    EL0 = 0b00,
    #[default]
    EL1 = 0b01,
    EL2 = 0b10,
    EL3 = 0b11,
}

#[bitsize(1)]
#[derive(Copy, Clone, Default, FromBits, Debug)]
/// Architectural mode, part of [`PSTATE`].
///
/// We only support `Aarch64` mode, but add an enum for it for completeness.
pub enum ArchMode {
    #[default]
    _64 = 0,
    _32 = 1,
}

#[bitsize(1)]
#[derive(Copy, Clone, Default, FromBits, Debug)]
/// Stack register selector, part of [`PSTATE`].
pub enum SpSel {
    #[default]
    SpEl0 = 0,
    Current = 1,
}

#[bitsize(4)]
#[derive(Copy, Clone, FromBits, Default, Debug)]
/// Processing Element (PE) mode.
pub enum Mode {
    EL0 = 0b0000,
    EL1t = 0b0100,
    #[default]
    EL1h = 0b0101,
    EL1tNV = 0b1000,
    EL1hNV = 0b1001,
    #[fallback]
    Undefined = 0b1011,
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, PartialEq, Eq, FromBits, DebugBits)]
/// Condition flags pseudo-register
pub struct NZCV {
    pub _padding2: u28,
    pub fields: NZCVFields,
    pub _padding: u32,
}

#[bitsize(4)]
#[derive(Default, Copy, Clone, PartialEq, Eq, FromBits, DebugBits)]
pub struct NZCVFields {
    /// Overflow condition flag. (bit `[28]`)
    pub V: bool,
    /// Carry condition flag. (bit `[29]`)
    pub C: bool,
    /// Zero condition flag. (bit `[30]`)
    pub Z: bool,
    /// Negative condition flag. (bit `[31]`)
    pub N: bool,
}

#[bitsize(4)]
#[derive(Default, Copy, Clone, PartialEq, Eq, FromBits, DebugBits)]
pub struct DAIFFields {
    pub F: bool,
    pub I: bool,
    pub A: bool,
    pub D: bool,
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, FromBits, DebugBits)]
/// Saved status register (`SPSR_ELx`).
pub struct SavedProgramStatusRegister {
    pub M: Mode,
    pub nRW: ArchMode,
    pub DAIF: DAIFFields,
    pub _btype: u2,
    pub _ssbs: u1,
    pub _allint: u1,
    pub __res: u6,
    pub IL: bool,
    pub SS: bool,
    pub _pan: u1,
    pub _uao: u1,
    pub _dit: u1,
    pub _tco: u1,
    pub __res0: u2,
    pub NZCV: NZCVFields,
    pub _pm: u1,
    pub _ppend: u1,
    pub _exlock: u1,
    pub _pacm: u1,
    pub _uinj: u1,
    pub _padding: u28,
}

#[bitsize(64)]
#[derive(Default, DebugBits)]
#[allow(non_snake_case)]
/// `PSTATE` isn't an architectural register for `ARMv8-A`. Its bit fields are
/// accessed through special-purpose registers.
///
/// The special registers are:
///
/// | Special purpose register | Description                                                                                     | `PSTATE` fields |
/// | ------------------------ | ----------------------------------------------------------------------------------------------- | --------------- |
/// | `CurrentEL`              | Holds the current Exception level.                                                              | `EL`            |
/// | `DAIF`                   | Specifies the current interrupt mask bits.                                                      | `D, A, I, F`    |
/// | `DAIFSet`                | Sets any of the `PSTATE.{D,A, I, F}` bits to `1`                                                | `D, A, I, F`    |
/// | `DAIFClr`                | Sets any of the `PSTATE.{D,A, I, F}` bits to `0`                                                | `D, A, I, F`    |
/// | `NZCV`                   | Holds the condition flags.                                                                      | `N, Z, C, V`    |
/// | `SPSel`                  | At `EL1` or higher, this selects between the `SP` for the current Exception level and `SP_EL0`. | `SP`            |
pub struct PSTATE {
    pub SP: SpSel,
    pub nRW: ArchMode,
    pub EL: ExceptionLevel,
    pub IL: bool,
    pub SS: bool,
    pub DAIF: DAIFFields,
    pub NZCV: NZCVFields,
    pub _res0: u50,
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
pub enum ExitRequest {
    Exception(Exception),
}

#[repr(C)]
#[derive(Default, Debug)]
pub struct ExecutionState {
    /// Regular registers.
    pub registers: RegisterFile,
    /// Vector (SIMD) registers.
    pub vector_registers: [(u64, u64); 32],
    /// Process Element state.
    pub pstate: PSTATE,
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
        &self,
        builder: &mut FunctionBuilder,
        registers: &mut IndexMap<bad64::Reg, Variable>,
        sys_registers: &mut IndexMap<bad64::SysReg, Variable>,
    ) {
        use bad64::{Reg, SysReg};

        let memflags = MemFlags::trusted().with_endianness(codegen::ir::Endianness::Little);
        macro_rules! reg_field {
            ($($field:ident$([$index:expr])? => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iconst(I64, std::ptr::addr_of!(self.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field) $(+ $index * std::mem::size_of::<u128>())*;
                    let value = builder.ins().load(I64, memflags, addr, i32::try_from(offset).unwrap());
                    let var = Variable::new(registers.len() + sys_registers.len());
                    assert!(!registers.contains_key(&$bad_reg));
                    registers.insert($bad_reg, var);
                    builder.declare_var(var, I64);
                    builder.def_var(var, value);
                )*
            }};
            (sys $($field:ident => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iconst(I64, std::ptr::addr_of!(self.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    let value = builder.ins().load(I64, memflags, addr, i32::try_from(offset).unwrap());
                    let var = Variable::new(registers.len() + sys_registers.len());
                    assert!(!sys_registers.contains_key(&$bad_sys_reg));
                    sys_registers.insert($bad_sys_reg, var);
                    builder.declare_var(var, I64);
                    builder.def_var(var, value);
                )*
            }};
        }
        reg_field! { sys
            ttbr0_el1 => SysReg::TTBR0_EL1,
            vttbr_el2 => SysReg::VTTBR_EL2,
            mair_el1 => SysReg::MAIR_EL1,
            //reg_field! { sys id_aa64mmfr0_el1 => SysReg::ID_AA64MMFR0_EL1 };
            sp_el0 => SysReg::SP_EL0,
            sp_el1 => SysReg::SP_EL1,
            sp_el2 => SysReg::SP_EL2,
            // sp_el3 => SysReg::SP_EL3,
            // [ref:FIXME]: bad64 doesn't have an SP_EL3 variant.
            tcr_el1 => SysReg::TCR_EL1,
            sctlr_el1 => SysReg::SCTLR_EL1,
            sctlr_el2 => SysReg::SCTLR_EL2,
            sctlr_el3 => SysReg::SCTLR_EL3,
            cpacr_el1 => SysReg::CPACR_EL1,
            vbar_el1 => SysReg::VBAR_EL1,
            hcr_el2 => SysReg::HCR_EL2,
            scr_el3 => SysReg::SCR_EL3,
            vpidr_el2 => SysReg::VPIDR_EL2,
            vmpidr_el2 => SysReg::VMPIDR_EL2,
            spsr_el3 =>  SysReg::SPSR_EL3,
            elr_el1 => SysReg::ELR_EL1,
            elr_el2 => SysReg::ELR_EL2,
            elr_el3 => SysReg::ELR_EL3,
            spsr_el1 => SysReg::SPSR_EL1,
            esr_el1 => SysReg::ESR_EL1,
            nzcv => SysReg::NZCV,
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
            xzr => Reg::XZR,
            sp => Reg::SP,
        }
        let vector_addr = builder
            .ins()
            .iconst(I64, std::ptr::addr_of!(self.vector_registers) as i64);
        for i in 0_u32..=31 {
            let d_reg = bad64::Reg::from_u32(bad64::Reg::D0 as u32 + i).unwrap();
            assert!(!registers.contains_key(&d_reg));
            let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
            assert!(!registers.contains_key(&v_reg));
            let offset = i * std::mem::size_of::<(u64, u64)>() as u32;
            let offset = i32::try_from(offset).unwrap();
            {
                let d_value = builder.ins().load(I64, memflags, vector_addr, offset);
                let d_var = Variable::new(registers.len() + sys_registers.len());
                registers.insert(d_reg, d_var);
                builder.declare_var(d_var, I64);
                builder.def_var(d_var, d_value);
            }
            {
                let v_value = builder.ins().load(
                    I64,
                    memflags,
                    vector_addr,
                    offset + std::mem::size_of::<u64>() as i32,
                );
                let v_var = Variable::new(registers.len() + sys_registers.len());
                registers.insert(v_reg, v_var);
                builder.declare_var(v_var, I64);
                builder.def_var(v_var, v_value);
            }
        }
    }

    /// Generate JIT instructions to store register values back to `self`.
    ///
    /// Used as an epilogue of a translation block.
    pub fn save_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        registers: &IndexMap<bad64::Reg, Variable>,
        sys_registers: &IndexMap<bad64::SysReg, Variable>,
        write_to_sysreg: bool,
        write_to_simd: bool,
    ) {
        use bad64::{Reg, SysReg};

        let memflags = MemFlags::trusted().with_endianness(codegen::ir::Endianness::Little);
        macro_rules! reg_field {
            ($($field:ident$([$index:expr])? => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iconst(I64, std::ptr::addr_of!(self.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field) $(+ $index * std::mem::size_of::<u128>())*;
                    assert!(registers.contains_key(&$bad_reg));
                    let var = &registers[&$bad_reg];
                    let var_value = builder.use_var(*var);
                    builder.ins().store(memflags, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
            (sys $($field:ident$($conversion:expr)? => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iconst(I64, std::ptr::addr_of!(self.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    assert!(sys_registers.contains_key(&$bad_sys_reg));
                    let var = &sys_registers[&$bad_sys_reg];
                    let var_value = builder.use_var(*var);
                    builder.ins().store(memflags, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
        }

        if write_to_sysreg {
            reg_field! { sys
                ttbr0_el1 => SysReg::TTBR0_EL1,
                vttbr_el2 => SysReg::VTTBR_EL2,
                mair_el1 => SysReg::MAIR_EL1,
                // id_aa64mmfr0_el1 => SysReg::ID_AA64MMFR0_EL1,
                sp_el0 => SysReg::SP_EL0,
                sp_el1 => SysReg::SP_EL1,
                sp_el2 => SysReg::SP_EL2,
                // sp_el3 => SysReg::SP_EL3,
                // [ref:FIXME]: bad64 doesn't have an SP_EL3 variant.
                tcr_el1 => SysReg::TCR_EL1,
                sctlr_el1 => SysReg::SCTLR_EL1,
                sctlr_el2 => SysReg::SCTLR_EL2,
                sctlr_el3 => SysReg::SCTLR_EL3,
                cpacr_el1 => SysReg::CPACR_EL1,
                vbar_el1 => SysReg::VBAR_EL1,
                hcr_el2 => SysReg::HCR_EL2,
                scr_el3 => SysReg::SCR_EL3,
                vpidr_el2 => SysReg::VPIDR_EL2,
                vmpidr_el2 => SysReg::VMPIDR_EL2,
                spsr_el3 =>  SysReg::SPSR_EL3,
                elr_el1 => SysReg::ELR_EL1,
                elr_el2 => SysReg::ELR_EL2,
                elr_el3 => SysReg::ELR_EL3,
                spsr_el1 => SysReg::SPSR_EL1,
                esr_el1 => SysReg::ESR_EL1,
                nzcv => SysReg::NZCV,
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
            let vector_addr = builder
                .ins()
                .iconst(I64, std::ptr::addr_of!(self.vector_registers) as i64);
            for i in 0_u32..=31 {
                let offset = i * std::mem::size_of::<(u64, u64)>() as u32;
                let d_reg = bad64::Reg::from_u32(bad64::Reg::D0 as u32 + i).unwrap();
                let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
                assert!(registers.contains_key(&d_reg));
                assert!(registers.contains_key(&v_reg));
                let var = &registers[&d_reg];
                let low_bits_value = builder.use_var(*var);
                let offset = i32::try_from(offset).unwrap();
                builder
                    .ins()
                    .store(memflags, low_bits_value, vector_addr, offset);
                let var = &registers[&v_reg];
                let high_bits_value = builder.use_var(*var);
                builder.ins().store(
                    memflags,
                    high_bits_value,
                    vector_addr,
                    offset + std::mem::size_of::<u64>() as i32,
                );
            }
        }
    }

    pub const fn EL2_enabled(&self) -> bool {
        false
    }

    pub const fn have_el(&self, el: ExceptionLevel) -> bool {
        matches!(el, ExceptionLevel::EL0 | ExceptionLevel::EL1)
    }

    pub fn vbar_elx(&self) -> u64 {
        match self.pstate.EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.registers.vbar_el1,
            other => unimplemented!("other vbar for {other:?}"),
        }
    }

    pub fn set_elr_elx(&mut self, val: u64) {
        match self.pstate.EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.registers.elr_el1 = val,
            ExceptionLevel::EL2 => self.registers.elr_el2 = val,
            ExceptionLevel::EL3 => self.registers.elr_el3 = val,
        }
    }

    pub fn psr_from_PSTATE(&self) -> SavedProgramStatusRegister {
        let mut spsr = SavedProgramStatusRegister::from(0);
        spsr.set_NZCV(self.registers.nzcv.fields());
        spsr.set_DAIF(self.pstate.DAIF());
        spsr.set_SS(self.pstate.SS());
        spsr.set_IL(self.pstate.IL());
        spsr.set_nRW(ArchMode::_64);
        spsr.set_M(Mode::EL1h);
        spsr
    }

    pub fn set_spsr_elx(&mut self, val: SavedProgramStatusRegister) {
        match self.pstate.EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.registers.spsr_el1 = val,
            ExceptionLevel::EL2 => self.registers.spsr_el2 = val,
            ExceptionLevel::EL3 => self.registers.spsr_el3 = val,
        }
    }
}

bitflags::bitflags! {
    /// Bitflag of architectural features, currently does not affect emulation at all.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct ArchFeatures: u64 {
        const FEAT_LSE = 0b00000001;
    }
}

/// Default value is `FEAT_LSE`.
impl Default for ArchFeatures {
    fn default() -> Self {
        Self::FEAT_LSE
    }
}
