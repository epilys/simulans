// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

#![allow(non_camel_case_types, clippy::upper_case_acronyms)]

use codegen::ir::types::{I64, I8};
use cranelift::prelude::*;
use cranelift_module::Module;

use crate::{cpu_state::SysReg, devices::timer, jit::BlockTranslator, machine::Armv8AMachine};

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
            unimplemented!(
                "{op} unimplemented sysreg {reg:?}",
                op = if write { "write" } else { "read" }
            );
        })
    }

    pub fn read_sysreg(&mut self, reg: &SysReg) -> Value {
        match reg {
            SysReg::NZCV => NZCV::generate_read(self),
            SysReg::DAIF => DAIF::generate_read(self),
            SysReg::CurrentEL => CurrentEl::generate_read(self),
            SysReg::SpSel => SPSel::generate_read(self),
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
            SysReg::TPIDR_EL0 => register_field!(read self, mmu_registers.tpidr_el0),
            SysReg::TPIDRRO_EL0 => register_field!(read self, mmu_registers.tpidrro_el0),
            SysReg::TPIDR_EL1 => register_field!(read self, mmu_registers.tpidr_el1),
            SysReg::CONTEXTIDR_EL1 => register_field!(read self, mmu_registers.contextidr_el1),
            SysReg::ESR_EL1 => register_field!(read self, exception_registers.esr_el1),
            SysReg::ESR_EL2 => register_field!(read self, exception_registers.esr_el2),
            SysReg::ESR_EL3 => register_field!(read self, exception_registers.esr_el3),
            SysReg::VBAR_EL1 => register_field!(read self, exception_registers.vbar_el1),
            SysReg::VBAR_EL2 => register_field!(read self, exception_registers.vbar_el2),
            SysReg::VBAR_EL3 => register_field!(read self, exception_registers.vbar_el3),
            SysReg::CPTR_EL3 => register_field!(read self, exception_registers.cptr_el3),
            SysReg::ELR_EL1 => register_field!(read self, exception_registers.elr_el1),
            SysReg::ELR_EL2 => register_field!(read self, exception_registers.elr_el2),
            SysReg::ELR_EL3 => register_field!(read self, exception_registers.elr_el3),
            SysReg::SCTLR_EL1 => register_field!(read self, control_registers.sctlr_el1),
            SysReg::SCTLR_EL2 => register_field!(read self, control_registers.sctlr_el2),
            SysReg::SCTLR_EL3 => register_field!(read self, control_registers.sctlr_el3),
            SysReg::CPACR_EL1 => register_field!(read self, control_registers.cpacr_el1),
            SysReg::HCR_EL2 => register_field!(read self, control_registers.hcr_el2),
            SysReg::SCR_EL3 => register_field!(read self, control_registers.scr_el3),
            SysReg::CNTFRQ_EL0 => self.timer_read(timer::RegisterID::CNTFRQ_EL0),
            SysReg::CNTKCTL_EL1 => register_field!(read self, timer_registers.cntkctl_el1),
            SysReg::CNTV_CTL_EL0 => self.timer_read(timer::RegisterID::CNTV_CTL_EL0),
            SysReg::CNTV_CVAL_EL0 => self.timer_read(timer::RegisterID::CNTV_CVAL_EL0),
            SysReg::CNTP_CTL_EL0 => self.timer_read(timer::RegisterID::CNTP_CTL_EL0),
            SysReg::CNTP_CVAL_EL0 => self.timer_read(timer::RegisterID::CNTP_CVAL_EL0),
            SysReg::CNTP_TVAL_EL0 => self.timer_read(timer::RegisterID::CNTP_TVAL_EL0),
            SysReg::CNTVCT_EL0 => self.timer_read(timer::RegisterID::CNTVCT_EL0),
            SysReg::OSLAR_EL1 | SysReg::OSDLR_EL1 => {
                // Debugger locks, ignore
                self.builder.ins().iconst(I64, 0)
            }
            SysReg::DBGBVR0_EL1
            | SysReg::DBGBCR0_EL1
            | SysReg::DBGBVR1_EL1
            | SysReg::DBGBCR1_EL1
            | SysReg::DBGBVR2_EL1
            | SysReg::DBGBCR2_EL1
            | SysReg::DBGBVR3_EL1
            | SysReg::DBGBCR3_EL1
            | SysReg::DBGBVR4_EL1
            | SysReg::DBGBCR4_EL1
            | SysReg::DBGBVR5_EL1
            | SysReg::DBGBCR5_EL1
            | SysReg::DBGWVR0_EL1
            | SysReg::DBGWCR0_EL1
            | SysReg::DBGWVR1_EL1
            | SysReg::DBGWCR1_EL1
            | SysReg::DBGWVR2_EL1
            | SysReg::DBGWCR2_EL1
            | SysReg::DBGWVR3_EL1
            | SysReg::DBGWCR3_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::ID_AA64MMFR0_EL1 => {
                register_field!(read self, id_registers.id_aa64mmfr0_el1)
            }
            SysReg::ID_AA64MMFR2_EL1 => register_field!(read self, id_registers.id_aa64mmfr2_el1),
            SysReg::ID_AA64ISAR0_EL1 => register_field!(read self, id_registers.id_aa64isar0_el1),
            SysReg::ID_AA64ISAR1_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::ID_AA64ISAR2_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::MIDR_EL1 => register_field!(read self, id_registers.midr_el1),
            SysReg::MPIDR_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::CTR_EL0 => {
                // [ref:FIXME]: CTR_EL0
                self.builder.ins().iconst(I64, 0xb444c004)
            }
            SysReg::ID_AA64PFR0_EL1 => register_field!(read self, id_registers.id_aa64pfr0_el1),
            SysReg::ID_AA64PFR1_EL1 => register_field!(read self, id_registers.id_aa64pfr1_el1),
            SysReg::ID_AA64ZFR0_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::ID_AA64SMFR0_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::GMID_EL1 => self.builder.ins().iconst(I64, 0),
            // [ref:TODO]: ID_AA64DFR0_EL1 AArch64 Debug Feature Register 0
            SysReg::ID_AA64DFR0_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::ID_AA64MMFR1_EL1 => register_field!(read self, id_registers.id_aa64mmfr1_el1),
            SysReg::ID_AA64MMFR3_EL1 => register_field!(read self, id_registers.id_aa64mmfr3_el1),
            SysReg::DCZID_EL0 => register_field!(read self, id_registers.dczid_el0),
            SysReg::CLIDR_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::REVIDR_EL1 => self.builder.ins().iconst(I64, 0),
            SysReg::ID_AA64DFR1_EL1 => self.builder.ins().iconst(I64, 0),
            // Aarch32 registers:
            SysReg::ID_DFR0_EL1
            | SysReg::ID_DFR1_EL1
            | SysReg::ID_ISAR0_EL1
            | SysReg::ID_ISAR1_EL1
            | SysReg::ID_ISAR2_EL1
            | SysReg::ID_ISAR3_EL1
            | SysReg::ID_ISAR4_EL1
            | SysReg::ID_ISAR5_EL1
            | SysReg::ID_ISAR6_EL1
            | SysReg::ID_MMFR0_EL1
            | SysReg::ID_MMFR1_EL1
            | SysReg::ID_MMFR2_EL1
            | SysReg::ID_MMFR3_EL1
            | SysReg::ID_MMFR4_EL1
            | SysReg::ID_MMFR5_EL1
            | SysReg::ID_PFR0_EL1
            | SysReg::ID_PFR1_EL1
            | SysReg::ID_PFR2_EL1
            | SysReg::MVFR0_EL1
            | SysReg::MVFR1_EL1
            | SysReg::MVFR2_EL1 => self.builder.ins().iconst(I64, 0),
            // [ref:FEAT_RNG]
            SysReg::RNDRRS => RNDRRS::generate_read(self),
            SysReg::RNDR => RNDRRS::generate_read(self),
            SysReg::TPIDR2_EL0 => register_field!(read self, mmu_registers.tpidr2_el0),
            _ => {
                let var = *self.sysreg_to_var(reg, false);
                self.builder.use_var(var)
            }
        }
    }

    fn timer_read(&mut self, reg: timer::RegisterID) -> Value {
        let sigref = {
            let mut sig = self.module.make_signature();
            sig.params
                .push(AbiParam::new(self.module.target_config().pointer_type()));
            sig.params.push(AbiParam::new(I8));
            sig.returns.push(AbiParam::new(I64));
            self.builder.import_signature(sig)
        };
        let reg = self.builder.ins().iconst(I8, i64::from(reg as u8));
        let callee = self
            .builder
            .ins()
            .iconst(I64, timer::timer_register_read as usize as i64);
        let call = self
            .builder
            .ins()
            .call_indirect(sigref, callee, &[self.machine_ptr, reg]);
        self.builder.inst_results(call)[0]
    }

    fn timer_write(&mut self, reg: timer::RegisterID, value: Value) {
        let sigref = {
            let mut sig = self.module.make_signature();
            sig.params
                .push(AbiParam::new(self.module.target_config().pointer_type()));
            sig.params.push(AbiParam::new(I8));
            sig.params.push(AbiParam::new(I64));
            self.builder.import_signature(sig)
        };
        let reg = self.builder.ins().iconst(I8, i64::from(reg as u8));
        let callee = self
            .builder
            .ins()
            .iconst(I64, timer::timer_register_write as usize as i64);
        let call =
            self.builder
                .ins()
                .call_indirect(sigref, callee, &[self.machine_ptr, reg, value]);
        self.builder.inst_results(call);
    }

    pub fn write_sysreg(&mut self, reg: &SysReg, value: Value) {
        self.write_to_sysreg = true;
        match reg {
            SysReg::NZCV => NZCV::generate_write(self, value),
            SysReg::DAIFSet => DAIFSet::generate_write(self, value),
            SysReg::DAIFClr => DAIFClr::generate_write(self, value),
            SysReg::CurrentEL => CurrentEl::generate_write(self, value),
            SysReg::SpSel => SPSel::generate_write(self, value),
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
            SysReg::TPIDR_EL0 => register_field!(write self, value, mmu_registers.tpidr_el0),
            SysReg::TPIDRRO_EL0 => register_field!(write self, value, mmu_registers.tpidrro_el0),
            SysReg::TPIDR_EL1 => register_field!(write self, value, mmu_registers.tpidr_el1),
            SysReg::ESR_EL1 => register_field!(write self, value, exception_registers.esr_el1),
            SysReg::ESR_EL2 => register_field!(write self, value, exception_registers.esr_el2),
            SysReg::ESR_EL3 => register_field!(write self, value, exception_registers.esr_el3),
            SysReg::VBAR_EL1 => register_field!(write self, value, exception_registers.vbar_el1),
            SysReg::VBAR_EL2 => register_field!(write self, value, exception_registers.vbar_el2),
            SysReg::VBAR_EL3 => register_field!(write self, value, exception_registers.vbar_el3),
            SysReg::CPTR_EL3 => register_field!(write self, value, exception_registers.cptr_el3),
            SysReg::ELR_EL1 => register_field!(write self, value, exception_registers.elr_el1),
            SysReg::ELR_EL2 => register_field!(write self, value, exception_registers.elr_el2),
            SysReg::ELR_EL3 => register_field!(write self, value, exception_registers.elr_el3),
            SysReg::SCTLR_EL1 => register_field!(write self, value, control_registers.sctlr_el1),
            SysReg::SCTLR_EL2 => register_field!(write self, value, control_registers.sctlr_el2),
            SysReg::SCTLR_EL3 => register_field!(write self, value, control_registers.sctlr_el3),
            SysReg::CPACR_EL1 => register_field!(write self, value, control_registers.cpacr_el1),
            SysReg::HCR_EL2 => register_field!(write self, value, control_registers.hcr_el2),
            SysReg::SCR_EL3 => register_field!(write self, value, control_registers.scr_el3),
            SysReg::CNTKCTL_EL1 => {
                register_field!(write self, value, timer_registers.cntkctl_el1)
            }
            SysReg::CNTV_CTL_EL0 => self.timer_write(timer::RegisterID::CNTV_CTL_EL0, value),
            SysReg::CNTV_CVAL_EL0 => self.timer_write(timer::RegisterID::CNTV_CVAL_EL0, value),
            SysReg::CNTP_CTL_EL0 => self.timer_write(timer::RegisterID::CNTP_CTL_EL0, value),
            SysReg::CNTP_CVAL_EL0 => self.timer_write(timer::RegisterID::CNTP_CVAL_EL0, value),
            SysReg::CNTP_TVAL_EL0 => self.timer_write(timer::RegisterID::CNTP_TVAL_EL0, value),
            SysReg::APDAKEYHI_EL1
            | SysReg::APDAKEYLO_EL1
            | SysReg::APDBKEYHI_EL1
            | SysReg::APDBKEYLO_EL1
            | SysReg::APIBKEYHI_EL1
            | SysReg::APGAKEYHI_EL1
            | SysReg::APGAKEYLO_EL1
            | SysReg::APIAKEYHI_EL1
            | SysReg::APIBKEYLO_EL1
            | SysReg::APIAKEYLO_EL1 => {
                // [ref:pointer_auth]
            }
            SysReg::OSLAR_EL1 | SysReg::OSDLR_EL1 => {
                // Debugger locks, ignore
            }
            SysReg::DBGBVR0_EL1
            | SysReg::DBGBCR0_EL1
            | SysReg::DBGBVR1_EL1
            | SysReg::DBGBCR1_EL1
            | SysReg::DBGBVR2_EL1
            | SysReg::DBGBCR2_EL1
            | SysReg::DBGBVR3_EL1
            | SysReg::DBGBCR3_EL1
            | SysReg::DBGBVR4_EL1
            | SysReg::DBGBCR4_EL1
            | SysReg::DBGBVR5_EL1
            | SysReg::DBGBCR5_EL1
            | SysReg::DBGWVR0_EL1
            | SysReg::DBGWCR0_EL1
            | SysReg::DBGWVR1_EL1
            | SysReg::DBGWCR1_EL1
            | SysReg::DBGWVR2_EL1
            | SysReg::DBGWCR2_EL1
            | SysReg::DBGWVR3_EL1
            | SysReg::DBGWCR3_EL1 => {
                // Debugger stuff, ignore
            }
            SysReg::PIRE0_EL1 => register_field!(write self, value, mmu_registers.pire0_el1),
            SysReg::PIR_EL1 => register_field!(write self, value, mmu_registers.pir_el1),
            SysReg::TCR2_EL1 => {}
            SysReg::TPIDR2_EL0 => register_field!(write self, value, mmu_registers.tpidr2_el0),
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
        let current_value = pstate_field!(read jit, mask = 0b1111 << 5);
        jit.builder.ins().ishl_imm(current_value, 1)
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        let value = jit.builder.ins().ishl_imm(value, 5);
        pstate_field!(write jit, value, mask = 0b1111 << 4)
    }
}

pub struct DAIFSet;

impl SystemRegister for DAIFSet {
    fn generate_read(_jit: &mut BlockTranslator<'_>) -> Value {
        panic!()
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        let value = jit.builder.ins().ishl_imm(value, 5);
        let current_value = pstate_field!(read jit, mask = 0b1111 << 5);
        let new_value = jit.builder.ins().bor(current_value, value);
        pstate_field!(write jit, new_value, mask = 0b1111 << 5)
    }
}

pub struct DAIFClr;

impl SystemRegister for DAIFClr {
    fn generate_read(_jit: &mut BlockTranslator<'_>) -> Value {
        panic!()
    }

    fn generate_write(jit: &mut BlockTranslator<'_>, value: Value) {
        let value = jit.builder.ins().ishl_imm(value, 5);
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

pub struct RNDRRS;

impl SystemRegister for RNDRRS {
    fn generate_read(jit: &mut BlockTranslator<'_>) -> Value {
        extern "C" fn rand() -> u64 {
            getrandom::u64().unwrap_or(0)
        }
        let sigref = {
            let mut sig = jit.module.make_signature();
            sig.returns.push(AbiParam::new(I64));
            jit.builder.import_signature(sig)
        };
        let callee = jit.builder.ins().iconst(I64, rand as usize as i64);
        let call = jit.builder.ins().call_indirect(sigref, callee, &[]);
        let nzcv = jit.builder.ins().iconst(I64, 0);
        NZCV::generate_write(jit, nzcv);
        jit.builder.inst_results(call)[0]
    }

    fn generate_write(_: &mut BlockTranslator<'_>, _: Value) {}
}
