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

use bilge::prelude::*;
use cranelift::prelude::*;
use indexmap::IndexMap;

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
    pub sp_el0: u64,
    pub sp_el1: u64,
    pub sp_el2: u64,
    pub sp_el3: u64,
    pub ttbr0_el1: u64,
    pub mair_el1: u64,
    pub id_aa64mmfr0_el1: u64,
    pub tcr_el1: u64,
    pub sctlr_el1: u64,
    pub cpacr_el1: u64,
    pub vbar_el1: u64,
    // pub spsr_el1: SavedProgramStatusRegister,
    // pub spsr_el2: SavedProgramStatusRegister,
    // pub spsr_el3: SavedProgramStatusRegister,
    // pub elr_el1: u64,
    // pub elr_el2: u64,
    // pub elr_el3: u64,
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
pub enum SpSel {
    #[default]
    Current,
    SpEl0,
}

#[repr(C)]
#[derive(Default, Debug)]
pub struct ProcessorState {
    pub spsr: SavedProgramStatusRegister,
    pub el: CurrentEl,
    pub sp: SpSel,
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

// #[repr(C)]
#[bitsize(32)]
#[derive(Default, FromBits, DebugBits)]
pub struct SavedProgramStatusRegister {
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
    /// When `FEAT_SSBS` is implemented: Speculative Store Bypass,  otherwise reserved zero. (bit `[23]`)
    pub ssbs: u1,
    /// When FEAT_PAN is implemented, Privileged Access Never, otherwise reserved zero. (bit `[22]`)
    pub pan: u1,
    /// When FEAT_DIT is implemented: Data Independent Timing, otherwise reserved zero . (bit `[21]`)
    pub dit: u1,
    /// Illegal Execution state. (bit `[20]`)
    pub il: bool,
    /// Greater than or Equal flags. (bits `[19:16]`)
    pub ge: u4,
    /// If-then bits `[7:2]` part. (bits `[7:2]`)
    pub it_b: u6,
    /// Big Endianness. (bit `[9]`)
    pub e: bool,
    /// SError exception mask. "Set to the value of PSTATE.A on taking an exception to the current mode, and copied to PSTATE.A on executing an exception return operation in the current mode". (bit `[8]`)
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
pub struct ExecutionState {
    pub registers: RegisterFile,
    pub pstate: ProcessorState,
}

impl ExecutionState {
    /// Add JIT instructions to assign a variable for each register and set it with its value.
    pub fn load_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        registers: &mut IndexMap<bad64::Reg, Variable>,
        sys_registers: &mut IndexMap<bad64::SysReg, Variable>,
    ) {
        use bad64::{Reg, SysReg};

        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");
        macro_rules! decl_reg_field {
            ($($field:ident => $bad_reg:expr),*$(,)?) => {{
                $(
                    let value = builder.ins().iconst(int, self.registers.$field as i64);
                    let var = Variable::new(registers.len() + sys_registers.len());
                    assert!(!registers.contains_key(&$bad_reg));
                    registers.insert($bad_reg, var);
                    builder.declare_var(var, int);
                    builder.def_var(var, value);
                )*
            }};
            (sys $field:ident => $bad_sys_reg:expr) => {{
                let value = builder.ins().iconst(int, self.registers.$field as i64);
                let var = Variable::new(registers.len() + sys_registers.len());
                assert!(!sys_registers.contains_key(&$bad_sys_reg));
                sys_registers.insert($bad_sys_reg, var);
                builder.declare_var(var, int);
                builder.def_var(var, value);
            }};
        }
        decl_reg_field! { sys ttbr0_el1 => SysReg::TTBR0_EL1 };
        decl_reg_field! { sys mair_el1 => SysReg::MAIR_EL1 };
        //decl_reg_field! { sys id_aa64mmfr0_el1 => SysReg::ID_AA64MMFR0_EL1 };
        decl_reg_field! { sys tcr_el1 => SysReg::TCR_EL1 };
        decl_reg_field! { sys sctlr_el1 => SysReg::SCTLR_EL1 };
        decl_reg_field! { sys cpacr_el1 => SysReg::CPACR_EL1 };
        decl_reg_field! { sys vbar_el1 => SysReg::VBAR_EL1 };
        decl_reg_field! {
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
            sp_el0 => bad64::Reg::SP,
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

        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");
        let memflags = MemFlags::new().with_endianness(codegen::ir::Endianness::Little);
        macro_rules! read_reg_field {
            ($($field:ident => $bad_reg:expr),*$(,)?) => {{
                $(
                    let addr = builder.ins().iconst(int, std::ptr::addr_of!(self.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    assert!(registers.contains_key(&$bad_reg));
                    let var = &registers[&$bad_reg];
                    let var_value = builder.use_var(*var);
                    builder.ins().store(memflags, var_value, addr, i32::try_from(offset).unwrap());
                )*
            }};
            (sys $field:ident => $bad_sys_reg:expr) => {{
                    let addr = builder.ins().iconst(int, std::ptr::addr_of!(self.registers) as i64);
                    let offset = core::mem::offset_of!(RegisterFile, $field);
                    assert!(sys_registers.contains_key(&$bad_sys_reg));
                    let var = &sys_registers[&$bad_sys_reg];
                    let var_value = builder.use_var(*var);
                    builder.ins().store(memflags, var_value, addr, i32::try_from(offset).unwrap());
            }};
        }

        read_reg_field! { sys ttbr0_el1 => SysReg::TTBR0_EL1 };
        read_reg_field! { sys mair_el1 => SysReg::MAIR_EL1 };
        // read_reg_field! { sys id_aa64mmfr0_el1 => SysReg::ID_AA64MMFR0_EL1 };
        read_reg_field! { sys tcr_el1 => SysReg::TCR_EL1 };
        read_reg_field! { sys sctlr_el1 => SysReg::SCTLR_EL1 };
        read_reg_field! { sys cpacr_el1 => SysReg::CPACR_EL1 };
        read_reg_field! { sys vbar_el1 => SysReg::VBAR_EL1 };
        read_reg_field! {
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
            sp_el0 => bad64::Reg::SP,
        }
    }
}
