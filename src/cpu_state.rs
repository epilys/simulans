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

use cranelift::prelude::*;
use indexmap::IndexMap;

#[derive(Default, Debug)]
#[repr(C)]
pub struct RegisterState {
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
}

#[repr(C)]
#[derive(Default, Debug)]
pub struct CpuState {
    pub registers: RegisterState,
}

impl CpuState {
    /// Add JIT instructions to assign a variable for each register and set it with its value.
    pub fn load_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        variables: &mut IndexMap<bad64::Reg, Variable>,
    ) {
        use bad64::Reg;

        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");
        macro_rules! decl_reg_field {
            ($($field:ident => $bad_reg:expr),*$(,)?) => {{
                $(
                    let value = builder.ins().iconst(int, self.registers.$field as i64);
                    let var = Variable::new(variables.len());
                    assert!(!variables.contains_key(&$bad_reg));
                    variables.insert($bad_reg, var);
                    builder.declare_var(var, int);
                    builder.def_var(var, value);
                )*
            }};
        }
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
            sp_el0 => bad64::Reg::SP,
        }
    }

    /// Add JIT instructions to store register values back to `self`.
    pub fn save_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        variables: &IndexMap<bad64::Reg, Variable>,
    ) {
        use bad64::Reg;

        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");
        let memflags = MemFlags::new().with_endianness(codegen::ir::Endianness::Little);
        macro_rules! read_reg_field {
                ($($field:ident => $bad_reg:expr),*$(,)?) => {{
                    $(
                        let addr = builder.ins().iconst(int, std::ptr::addr_of!(self.registers) as i64);
                        let offset = core::mem::offset_of!(RegisterState, $field);
                        assert!(variables.contains_key(&$bad_reg));
                        let var = &variables[&$bad_reg];
                        let var_value = builder.use_var(*var);
                        builder.ins().store(memflags, var_value, addr, i32::try_from(offset).unwrap());
                    )*
                }};
            }

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
