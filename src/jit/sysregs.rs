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

#![allow(non_camel_case_types, clippy::upper_case_acronyms)]

use codegen::ir::types::I64;
use cranelift::prelude::*;

use crate::{jit::BlockTranslator, machine::Armv8AMachine};

impl BlockTranslator<'_> {
    #[inline]
    fn sysreg_to_var(&mut self, reg: &bad64::SysReg, write: bool) -> &Variable {
        self.write_to_sysreg |= write;
        self.sys_registers.get(reg).unwrap_or_else(|| {
            unimplemented!("unimplemented sysreg {reg:?}");
        })
    }

    pub fn read_sysreg(&mut self, reg: &bad64::SysReg) -> Value {
        match reg {
            bad64::SysReg::NZCV => NZCV::generate_read(self),
            bad64::SysReg::DAIFSET => DAIF::generate_read(self),
            bad64::SysReg::CURRENTEL => CurrentEl::generate_read(self),
            bad64::SysReg::PSTATE_SPSEL => SPSel::generate_read(self),
            _ => {
                let var = *self.sysreg_to_var(reg, false);
                self.builder.use_var(var)
            }
        }
    }

    pub fn write_sysreg(&mut self, reg: &bad64::SysReg, value: Value) {
        self.write_to_sysreg = true;
        match reg {
            bad64::SysReg::NZCV => NZCV::generate_write(self, value),
            bad64::SysReg::DAIFSET => DAIF::generate_write(self, value),
            bad64::SysReg::CURRENTEL => CurrentEl::generate_write(self, value),
            bad64::SysReg::PSTATE_SPSEL => SPSel::generate_write(self, value),
            _ => {
                let target = *self.sysreg_to_var(reg, true);
                self.builder.def_var(target, value);
            }
        }
    }
}

const TRUSTED_MEMFLAGS: MemFlags =
    MemFlags::trusted().with_endianness(codegen::ir::Endianness::Little);

pub trait SystemRegister {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value;

    fn generate_write(jit: &mut BlockTranslator<'_>, _: Value);
}

macro_rules! pstate_field {
    (read $jit:ident, mask = $mask:expr) => {{
        let addr = $jit.machine_ptr;
        let offset = std::mem::offset_of!(Armv8AMachine, cpu_state.registers.pstate);
        let offset = i32::try_from(offset).unwrap();
        let value = $jit.builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, offset);
        $jit.builder.ins().band_imm(value, $mask)
    }};
    (write $jit:ident, $value:ident, mask = $mask:expr) => {{
        let addr = $jit.machine_ptr;
        let offset = std::mem::offset_of!(Armv8AMachine, cpu_state.registers.pstate);
        let offset = i32::try_from(offset).unwrap();
        let pstate = $jit.builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, offset);
        let pstate = $jit.builder.ins().band_imm(pstate, !($mask));
        let pstate = $jit.builder.ins().bor(pstate, $value);
        $jit.builder
            .ins()
            .store(TRUSTED_MEMFLAGS, pstate, addr, offset);
    }};
}

pub struct NZCV;

impl SystemRegister for NZCV {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        pstate_field!(read jit, mask = 0b1111 << 28)
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        pstate_field!(write jit, value, mask = 0b1111 << 28)
    }
}

pub struct DAIF;

impl SystemRegister for DAIF {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        pstate_field!(read jit, mask = 0b1111 << 5)
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        pstate_field!(write jit, value, mask = 0b1111 << 5)
    }
}

pub struct CurrentEl;

impl SystemRegister for CurrentEl {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        pstate_field!(read jit, mask = 0b1100)
    }

    fn generate_write(_: &mut BlockTranslator<'_>, _: Value) {}
}

pub struct SPSel;

impl SystemRegister for SPSel {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        pstate_field!(read jit, mask = 0b1)
    }

    fn generate_write(_: &mut BlockTranslator<'_>, _: Value) {}
}
