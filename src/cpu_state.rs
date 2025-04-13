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

#![allow(non_snake_case)]

use bilge::prelude::*;
use codegen::ir::types::I64;
use cranelift::prelude::*;
use indexmap::IndexMap;
use num_traits::cast::FromPrimitive;

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
    /// Selected `SP` based on current Exception Level and PSTATE's SpSel.
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
    // pub spsr_el1: SavedProgramStatusRegister,
    // pub spsr_el2: SavedProgramStatusRegister,
    pub spsr_el3: SavedProgramStatusRegister,
    pub elr_el1: u64,
    pub elr_el2: u64,
    pub elr_el3: u64,
}

#[bitsize(2)]
#[derive(Default, FromBits, Debug)]
pub enum CurrentEl {
    EL0 = 0b00,
    EL1 = 0b01,
    #[default]
    EL2 = 0b10,
    EL3 = 0b11,
}

#[bitsize(1)]
#[derive(Default, FromBits, Debug)]
pub enum ArchMode {
    #[default]
    _64 = 0,
    _32 = 1,
}

#[bitsize(1)]
#[derive(Default, FromBits, Debug)]
pub enum SpSel {
    #[default]
    SpEl0 = 0,
    Current = 1,
}

#[bitsize(5)]
#[derive(Default, FromBits, Debug)]
pub enum Mode {
    User = 0b10000,
    FIQ = 0b10001,
    IRQ = 0b10010,
    Supervisor = 0b10011,
    Monitor = 0b10110,
    Abort = 0b10111,
    Hyp = 0b11010,
    #[fallback]
    Undefined = 0b11011,
    #[default]
    System = 0b11111,
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, FromBits, DebugBits)]
pub struct SavedProgramStatusRegister {
    pub _padding: u32,
    /// Negative condition flag. (bit `[31]`)
    pub n: bool,
    /// Zero condition flag. (bit `[30]`)
    pub z: bool,
    /// Carry condition flag. (bit `[29]`)
    pub c: bool,
    /// Overflow condition flag. (bit `[28]`)
    pub v: bool,
    /// Overflow or saturation condition flag. (bit `[27]`)
    pub q: bool,
    /// If-then bits `[1:0]` part. (bits `[26:25]`)
    pub it_a: u2,
    /// Reserved zero. (bit `[24]`)
    pub j: u1,
    /// When `FEAT_SSBS` is implemented: Speculative Store Bypass,  otherwise
    /// reserved zero. (bit `[23]`)
    pub ssbs: u1,
    /// When `FEAT_PAN` is implemented, Privileged Access Never, otherwise
    /// reserved zero. (bit `[22]`)
    pub pan: u1,
    /// When `FEAT_DIT` is implemented: Data Independent Timing, otherwise
    /// reserved zero . (bit `[21]`)
    pub dit: u1,
    /// Illegal Execution state. (bit `[20]`)
    pub il: bool,
    /// Greater than or Equal flags. (bits `[19:16]`)
    pub ge: u4,
    /// If-then bits `[7:2]` part. (bits `[7:2]`)
    pub it_b: u6,
    /// Big Endianness. (bit `[9]`)
    pub e: bool,
    /// SError exception mask. "Set to the value of `PSTATE.A` on taking an
    /// exception to the current mode, and copied to `PSTATE.A` on executing an
    /// exception return operation in the current mode". (bit `[8]`)
    pub a: bool,
    /// IRQ interrupt mask. (bit `[7]`)
    pub i: bool,
    /// FIQ interrupt mask. (bit `[6]`)
    pub f: bool,
    /// T32 Instruction set state. (bit `[5]`)
    pub t: bool,
    /// Mode. (bits `[4:0]`)
    pub m: Mode,
}

#[repr(C)]
#[derive(Default, Debug)]
#[allow(non_snake_case)]
pub struct PSTATE {
    /// Negative condition flag.
    pub N: u64,
    /// Zero condition flag.
    pub Z: u64,
    /// Carry condition flag.
    pub C: u64,
    /// oVerflow condition flag.
    pub V: u64,
    /// Debug mask bit.
    pub D: u64,
    /// SError mask bit.
    pub A: u64,
    /// IRQ mask bit.
    pub I: u64,
    /// FIQ mask bit.
    pub F: u64,
    /// Software Step bit.
    pub SS: u64,
    /// Illegal Execution state bit.
    pub IL: u64,
    /// (2) Exception level.
    pub EL: CurrentEl,
    /// Execution state
    /// ```text
    /// 0 = 64-bit
    /// 1 = 32-bit
    /// ```
    pub nRW: ArchMode,
    /// Stack pointer selector.
    /// ```text
    /// 0 = SP_EL0
    /// 1 = SP_ELn
    /// ```
    pub SP: SpSel,
}

#[repr(C)]
#[derive(Default, Debug)]
pub struct ExecutionState {
    pub registers: RegisterFile,
    pub vector_registers: [(u64, u64); 32],
    /// `PSTATE` isn't an architectural register for ARMv8. Its bit fields are
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
    pub pstate: PSTATE,
    pub spsr: SavedProgramStatusRegister,
    pub arch_features: ArchFeatures,
}

impl ExecutionState {
    /// Add JIT instructions to assign a variable for each register and set it
    /// with its value.
    pub fn load_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        registers: &mut IndexMap<bad64::Reg, Variable>,
        sys_registers: &mut IndexMap<bad64::SysReg, Variable>,
    ) {
        use bad64::{Reg, SysReg};

        macro_rules! reg_field {
            ($($field:ident$([$index:expr])? => $bad_reg:expr),*$(,)?) => {{
                $(
                    let value = builder.ins().iconst(I64, self.registers.$field$([$index])* as i64);
                    let var = Variable::new(registers.len() + sys_registers.len());
                    assert!(!registers.contains_key(&$bad_reg));
                    registers.insert($bad_reg, var);
                    builder.declare_var(var, I64);
                    builder.def_var(var, value);
                )*
            }};
            (sys $($field:ident$($conversion:expr)? => $bad_sys_reg:expr),*$(,)?) => {{
                $(
                    let value = builder.ins().iconst(I64, $($conversion)*(self.registers.$field) as u64 as i64);
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
            spsr_el3 u64::from =>  SysReg::SPSR_EL3,
            elr_el1 => SysReg::ELR_EL1,
            elr_el2 => SysReg::ELR_EL2,
            elr_el3 => SysReg::ELR_EL3,
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
        for i in 0_u32..=31 {
            let d_reg = bad64::Reg::from_u32(bad64::Reg::D0 as u32 + i).unwrap();
            assert!(!registers.contains_key(&d_reg));
            let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
            assert!(!registers.contains_key(&v_reg));
            {
                let d_value = builder
                    .ins()
                    .iconst(I64, self.vector_registers[i as usize].1 as i64);
                let d_var = Variable::new(registers.len() + sys_registers.len());
                registers.insert(d_reg, d_var);
                builder.declare_var(d_var, I64);
                builder.def_var(d_var, d_value);
            }
            {
                let v_value = builder
                    .ins()
                    .iconst(I64, self.vector_registers[i as usize].0 as i64);
                let v_var = Variable::new(registers.len() + sys_registers.len());
                registers.insert(v_reg, v_var);
                builder.declare_var(v_var, I64);
                builder.def_var(v_var, v_value);
            }
        }
    }

    /// Add JIT instructions to store register values back to `self`.
    pub fn save_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        registers: &IndexMap<bad64::Reg, Variable>,
        sys_registers: &IndexMap<bad64::SysReg, Variable>,
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
        };
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
        for i in 0_u32..=31 {
            let addr = builder
                .ins()
                .iconst(I64, std::ptr::addr_of!(self.vector_registers) as i64);
            let offset = i * std::mem::size_of::<(u64, u64)>() as u32;
            let d_reg = bad64::Reg::from_u32(bad64::Reg::D0 as u32 + i).unwrap();
            let v_reg = bad64::Reg::from_u32(bad64::Reg::V0 as u32 + i).unwrap();
            assert!(registers.contains_key(&d_reg));
            assert!(registers.contains_key(&v_reg));
            let var = &registers[&d_reg];
            let low_bits_value = builder.use_var(*var);
            let offset = i32::try_from(offset).unwrap();
            builder.ins().store(memflags, low_bits_value, addr, offset);
            let var = &registers[&v_reg];
            let high_bits_value = builder.use_var(*var);
            builder.ins().store(
                memflags,
                high_bits_value,
                addr,
                offset + std::mem::size_of::<u64>() as i32,
            );
        }
    }
}

bitflags::bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct ArchFeatures: u64 {
        const FEAT_LSE = 0b00000001;
    }
}

impl Default for ArchFeatures {
    fn default() -> Self {
        Self::FEAT_LSE
    }
}
