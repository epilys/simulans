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

use bad64::SysReg;
use codegen::ir::types::I64;
use cranelift::prelude::*;

use crate::{jit::BlockTranslator, machine::Armv8AMachine};

/// Helper struct to manage sysregs that bad64 doesn't support.
#[derive(Copy, Clone, Debug)]
pub struct SysRegEncoding {
    pub o0: u8,
    pub o1: u8,
    pub cm: u8,
    pub cn: u8,
    pub o2: u8,
}

macro_rules! register_field {
    (read $jit:ident, $($field:tt)*) => {{
        let addr = $jit.machine_ptr;
        let offset = std::mem::offset_of!(Armv8AMachine, cpu_state.$($field)*);
        let offset = i32::try_from(offset).unwrap();
        $jit.builder.ins().load(I64, TRUSTED_MEMFLAGS, addr, offset)
    }};
    (write $jit:ident, $val:expr, $($field:tt)*) => {{
        let addr = $jit.machine_ptr;
        let offset = std::mem::offset_of!(Armv8AMachine, cpu_state.$($field)*);
        let offset = i32::try_from(offset).unwrap();
        $jit.builder
            .ins()
            .store(TRUSTED_MEMFLAGS, $val, addr, offset);
    }};
}

impl BlockTranslator<'_> {
    #[inline]
    fn sysreg_to_var(&mut self, reg: &SysReg, write: bool) -> &Variable {
        self.write_to_sysreg |= write;
        self.sys_registers.get(reg).unwrap_or_else(|| {
            unimplemented!("unimplemented sysreg {reg:?}");
        })
    }

    pub fn read_sysreg(&mut self, reg: &SysReg) -> Value {
        match reg {
            SysReg::NZCV => NZCV::generate_read(self),
            SysReg::DAIFSET => DAIFSet::generate_read(self),
            SysReg::CURRENTEL => CurrentEl::generate_read(self),
            SysReg::PSTATE_SPSEL => SPSel::generate_read(self),
            // PMUSERENR_EL0, Performance Monitors User Enable Register
            SysReg::PMUSERENR_EL0 => self.builder.ins().iconst(I64, 0),
            // AMUSERENR_EL0, Activity Monitors User Enable Register
            // (We don't implement FEAT_AMUv1)
            SysReg::AMUSERENR_EL0 => self.builder.ins().iconst(I64, 0),
            // Monitor Debug System Control Register
            SysReg::MDSCR_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::TCR_EL1 => register_field!(read self, mmu_registers.tcr_el1),
            SysReg::TTBR0_EL1 => register_field!(read self, mmu_registers.ttbr0_el1),
            SysReg::TTBR1_EL1 => register_field!(read self, mmu_registers.ttbr1_el1),
            SysReg::VTTBR_EL2 => register_field!(read self, mmu_registers.vttbr_el2),
            SysReg::MAIR_EL1 => register_field!(read self, mmu_registers.mair_el1),
            SysReg::AMAIR_EL1 => register_field!(read self, mmu_registers.amair_el1),
            SysReg::CONTEXTIDR_EL1 => register_field!(read self, mmu_registers.contextidr_el1),
            SysReg::ESR_EL1 => register_field!(read self, exception_registers.esr_el1),
            SysReg::VBAR_EL1 => register_field!(read self, exception_registers.vbar_el1),
            SysReg::ELR_EL1 => register_field!(read self, exception_registers.elr_el1),
            SysReg::ELR_EL2 => register_field!(read self, exception_registers.elr_el2),
            SysReg::ELR_EL3 => register_field!(read self, exception_registers.elr_el3),
            _ => {
                let var = *self.sysreg_to_var(reg, false);
                self.builder.use_var(var)
            }
        }
    }

    pub fn write_sysreg(&mut self, reg: &SysReg, value: Value) {
        self.write_to_sysreg = true;
        match reg {
            SysReg::NZCV => NZCV::generate_write(self, value),
            SysReg::DAIFSET => DAIFSet::generate_write(self, value),
            SysReg::DAIFCLR => DAIFClr::generate_write(self, value),
            SysReg::CURRENTEL => CurrentEl::generate_write(self, value),
            SysReg::PSTATE_SPSEL => SPSel::generate_write(self, value),
            // PMUSERENR_EL0, Performance Monitors User Enable Register
            SysReg::PMUSERENR_EL0 => {}
            // AMUSERENR_EL0, Activity Monitors User Enable Register
            // (We don't implement FEAT_AMUv1)
            SysReg::AMUSERENR_EL0 => {}
            // Monitor Debug System Control Register
            SysReg::MDSCR_EL1 => {}
            SysReg::TCR_EL1 => register_field!(write self, value, mmu_registers.tcr_el1),
            SysReg::TTBR0_EL1 => register_field!(write self, value, mmu_registers.ttbr0_el1),
            SysReg::TTBR1_EL1 => register_field!(write self, value, mmu_registers.ttbr1_el1),
            SysReg::VTTBR_EL2 => register_field!(write self, value, mmu_registers.vttbr_el2),
            SysReg::MAIR_EL1 => register_field!(write self, value, mmu_registers.mair_el1),
            SysReg::AMAIR_EL1 => register_field!(write self, value, mmu_registers.amair_el1),
            SysReg::CONTEXTIDR_EL1 => {
                register_field!(write self, value, mmu_registers.contextidr_el1)
            }
            SysReg::ESR_EL1 => register_field!(write self, value, exception_registers.esr_el1),
            SysReg::VBAR_EL1 => register_field!(write self, value, exception_registers.vbar_el1),
            SysReg::ELR_EL1 => register_field!(write self, value, exception_registers.elr_el1),
            SysReg::ELR_EL2 => register_field!(write self, value, exception_registers.elr_el2),
            SysReg::ELR_EL3 => register_field!(write self, value, exception_registers.elr_el3),
            _ => {
                let target = *self.sysreg_to_var(reg, true);
                self.builder.def_var(target, value);
            }
        }
    }

    #[allow(non_snake_case)]
    /// Return [`Value`] for special registers.
    pub fn read_sysreg_o0_op1_CRn_CRm_op2(&mut self, reg: SysRegEncoding) -> Value {
        match reg {
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b111,
                o2: 0,
            } => {
                // ID_AA64MMFR0_EL1, AArch64 Memory Model Feature Register 0
                register_field!(read self, id_registers.id_aa64mmfr0_el1)
            }
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 7,
                o2: 2,
            } => {
                // ID_AA64MMFR2_EL1, AArch64 Memory Model Feature Register 2
                register_field!(read self, id_registers.id_aa64mmfr2_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0,
                o2: 0,
            } => {
                // MIDR_EL1
                register_field!(read self, id_registers.midr_el1)
            }
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 0,
                o2: 5,
            } => {
                // MPIDR_EL1, Multiprocessor Affinity Register
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 3,
                o1: 3,
                cm: 0,
                cn: 0,
                o2: 1,
            } => {
                // [ref:FIXME]: CTR_EL0
                self.builder.ins().iconst(I64, 0xb444c004)
            }
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 4,
                o2: 0,
            } => {
                // ID_AA64PFR0_EL1 AArch64 Processor Feature Register 0
                register_field!(read self, id_registers.id_aa64pfr0_el1)
            }
            SysRegEncoding {
                o0: 3,
                o1: 0,
                cm: 0,
                cn: 5,
                o2: 0,
            } => {
                // [ref:TODO]: ID_AA64DFR0_EL1 AArch64 Debug Feature Register 0
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b111,
                o2: 1,
            } => {
                // ID_AA64MMFR1_EL1, AArch64 Memory Model Feature Register 1
                register_field!(read self, id_registers.id_aa64mmfr1_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b111,
                o2: 0b11,
            } => {
                // ID_AA64MMFR3_EL1, AArch64 Memory Model Feature Register 3
                register_field!(read self, id_registers.id_aa64mmfr3_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b11,
                cm: 0,
                cn: 0,
                o2: 0b111,
            } => {
                // DCZID_EL0, Data Cache Zero ID Register
                register_field!(read self, id_registers.dczid_el0)
            }
            _other => unimplemented!(
                "unimplemented sysreg encoding: {:?} pc =0x{:x?}",
                reg,
                self.address,
            ),
        }
    }

    #[allow(non_snake_case)]
    /// Write [`Value`] for special registers.
    pub fn write_sysreg_o0_op1_CRn_CRm_op2(&mut self, reg: SysRegEncoding, value: Value) {
        match reg {
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b1010,
                cn: 0b0010,
                o2: 0b010,
            } => {
                // PIRE0_EL1, Permission Indirection Register 0 (EL1)
                register_field!(write self, value, mmu_registers.pire0_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b1010,
                cn: 0b0010,
                o2: 0b11,
            } => {
                // PIR_EL1, Permission Indirection Register 1 (EL1)
                register_field!(write self, value, mmu_registers.pir_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0010,
                cn: 0b0000,
                o2: 0b011,
            } => {
                // TCR2_EL1, Extended Translation Control Register (EL1)
            }
            _other => unimplemented!(
                "unimplemented sysreg encoding: {:?} pc =0x{:x?}",
                reg,
                self.address,
            ),
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

pub struct DAIFSet;

impl SystemRegister for DAIFSet {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        pstate_field!(read jit, mask = 0b1111 << 5)
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        let current_value = pstate_field!(read jit, mask = 0b1111 << 5);
        let new_value = jit.builder.ins().bor(current_value, value);
        pstate_field!(write jit, new_value, mask = 0b1111 << 5)
    }
}

pub struct DAIFClr;

impl SystemRegister for DAIFClr {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        pstate_field!(read jit, mask = 0b1111 << 5)
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        let current_value = pstate_field!(read jit, mask = 0b1111 << 5);
        let new_value = jit.builder.ins().band_not(current_value, value);
        pstate_field!(write jit, new_value, mask = 0b1111 << 5)
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
