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
    pub fn load_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        variables: &mut IndexMap<bad64::Reg, Variable>,
    ) {
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
            x0=> bad64::Reg::X0,
            x1=> bad64::Reg::X1,
            x2=> bad64::Reg::X2,
            x3=> bad64::Reg::X3,
            x4=> bad64::Reg::X4,
            x5=> bad64::Reg::X5,
            x6=> bad64::Reg::X6,
            x7=> bad64::Reg::X7,
            x8=> bad64::Reg::X8,
            x9=> bad64::Reg::X9,
            sp_el0 => bad64::Reg::SP,
        }
    }

    pub fn save_cpu_state(
        &self,
        builder: &mut FunctionBuilder,
        variables: &IndexMap<bad64::Reg, Variable>,
    ) {
        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");
        let memflags = cranelift::prelude::MemFlags::trusted()
            .with_endianness(codegen::ir::Endianness::Little);
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
            x0=> bad64::Reg::X0,
            x1=> bad64::Reg::X1,
            x2=> bad64::Reg::X2,
            x3=> bad64::Reg::X3,
            x4=> bad64::Reg::X4,
            x5=> bad64::Reg::X5,
            x6=> bad64::Reg::X6,
            x7=> bad64::Reg::X7,
            x8=> bad64::Reg::X8,
            x9=> bad64::Reg::X9,
            sp_el0 => bad64::Reg::SP,
        }
    }
}
