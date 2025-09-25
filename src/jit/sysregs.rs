// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

#![allow(non_camel_case_types, clippy::upper_case_acronyms)]

use bad64::SysReg;
use codegen::ir::types::I64;
use cranelift::prelude::*;
use cranelift_module::Module;

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
            unimplemented!(
                "{op} unimplemented sysreg {reg:?}",
                op = if write { "write" } else { "read" }
            );
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
            SysReg::TPIDR_EL0 => register_field!(read self, mmu_registers.tpidr_el0),
            SysReg::TPIDRRO_EL0 => register_field!(read self, mmu_registers.tpidrro_el0),
            SysReg::TPIDR_EL1 => register_field!(read self, mmu_registers.tpidr_el1),
            SysReg::CONTEXTIDR_EL1 => register_field!(read self, mmu_registers.contextidr_el1),
            SysReg::ESR_EL1 => register_field!(read self, exception_registers.esr_el1),
            SysReg::VBAR_EL1 => register_field!(read self, exception_registers.vbar_el1),
            SysReg::ELR_EL1 => register_field!(read self, exception_registers.elr_el1),
            SysReg::ELR_EL2 => register_field!(read self, exception_registers.elr_el2),
            SysReg::ELR_EL3 => register_field!(read self, exception_registers.elr_el3),
            SysReg::SCTLR_EL1 => register_field!(read self, control_registers.sctlr_el1),
            SysReg::SCTLR_EL2 => register_field!(read self, control_registers.sctlr_el2),
            SysReg::SCTLR_EL3 => register_field!(read self, control_registers.sctlr_el3),
            SysReg::CPACR_EL1 => register_field!(read self, control_registers.cpacr_el1),
            SysReg::HCR_EL2 => register_field!(read self, control_registers.hcr_el2),
            SysReg::SCR_EL3 => register_field!(read self, control_registers.scr_el3),
            SysReg::CNTFRQ_EL0 => register_field!(read self, timer_registers.cntfrq_el0),
            SysReg::CNTKCTL_EL1 => register_field!(read self, timer_registers.cntkctl_el1),
            SysReg::CNTV_CTL_EL0 => register_field!(read self, timer_registers.cntv_ctl_el0),
            SysReg::CNTV_CVAL_EL0 => register_field!(read self, timer_registers.cntv_cval_el0),
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
            SysReg::TPIDR_EL0 => register_field!(write self, value, mmu_registers.tpidr_el0),
            SysReg::TPIDRRO_EL0 => register_field!(write self, value, mmu_registers.tpidrro_el0),
            SysReg::TPIDR_EL1 => register_field!(write self, value, mmu_registers.tpidr_el1),
            SysReg::ESR_EL1 => register_field!(write self, value, exception_registers.esr_el1),
            SysReg::VBAR_EL1 => register_field!(write self, value, exception_registers.vbar_el1),
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
            SysReg::CNTV_CTL_EL0 => {
                register_field!(write self, value, timer_registers.cntv_ctl_el0)
            }
            SysReg::CNTV_CVAL_EL0 => {
                register_field!(write self, value, timer_registers.cntv_cval_el0)
            }
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
                cn: 0b110,
                o2: 0,
            } => {
                // ID_AA64ISAR0_EL1, AArch64 Instruction Set Attribute Register 0
                register_field!(read self, id_registers.id_aa64isar0_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b110,
                o2: 0b1,
            } => {
                // ID_AA64ISAR1_EL1, AArch64 Instruction Set Attribute Register 1
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b110,
                o2: 0b10,
            } => {
                // ID_AA64ISAR2_EL1, AArch64 Instruction Set Attribute Register 2
                self.builder.ins().iconst(I64, 0)
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
                o0: 0b11,
                o1: 0b11,
                cm: 0b1110,
                cn: 0,
                o2: 0b10,
            } => {
                // CNTVCT_EL0, Counter-timer Virtual Count Register
                // register_field!(read self, timer_registers.cntvct_el0)
                extern "C" fn count() -> u64 {
                    use std::sync::LazyLock;

                    static NOW: LazyLock<std::time::Instant> =
                        LazyLock::new(std::time::Instant::now);

                    NOW.elapsed().as_nanos() as u64
                }
                let sigref = {
                    let mut sig = self.module.make_signature();
                    sig.returns.push(AbiParam::new(I64));
                    self.builder.import_signature(sig)
                };
                let callee = self.builder.ins().iconst(I64, count as usize as i64);
                let call = self.builder.ins().call_indirect(sigref, callee, &[]);
                self.builder.inst_results(call)[0]
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
                cn: 4,
                o2: 1,
            } => {
                // ID_AA64PFR1_EL1, AArch64 Processor Feature Register 1
                register_field!(read self, id_registers.id_aa64pfr1_el1)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b100,
                o2: 0b100,
            } => {
                // ID_AA64ZFR0_EL1, SVE Feature ID Register 0
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b100,
                o2: 0b101,
            } => {
                // ID_AA64SMFR0_EL1, SME Feature ID Register 0
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b1,
                cm: 0,
                cn: 0,
                o2: 0b100,
            } => {
                // GMID_EL1, Multiple tag transfer ID Register
                self.builder.ins().iconst(I64, 0)
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
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0001,
                o2: 0b111,
            } => {
                // ID_MMFR3_EL1, AArch32 Memory Model Feature Register 3
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b000,
                cm: 0b0000,
                cn: 0b0011,
                o2: 0b110,
            } => {
                // ID_MMFR5_EL1, AArch32 Memory Model Feature Register 5
                self.builder.ins().iconst(I64, 0)
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
            SysRegEncoding {
                o0: 0b11,
                o1: 0b1,
                cm: 0,
                cn: 0,
                o2: 0b1,
            } => {
                // CLIDR_EL1, Cache Level ID Register
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0,
                o2: 0b110,
            } => {
                // REVIDR_EL1, Revision ID Register
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0,
                cm: 0,
                cn: 0b101,
                o2: 0b1,
            } => {
                // ID_AA64DFR1_EL1, AArch64 Debug Feature Register 1
                self.builder.ins().iconst(I64, 0)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b0010,
                cn: 0b0100,
                o2: 0b001,
            } => {
                // [ref:FEAT_RNG]
                // RNDRRS, Random Number Full Entropy
                RNDRRS::generate_read(self)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b0010,
                cn: 0b0100,
                o2: 0b000,
            } => {
                // RNDR, Random Number
                RNDRRS::generate_read(self)
            }
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b1101,
                cn: 0b0000,
                o2: 0b101,
            } => {
                register_field!(read self, mmu_registers.tpidr2_el0)
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
            SysRegEncoding {
                o0: 0b11,
                o1: 0b011,
                cm: 0b1101,
                cn: 0b0000,
                o2: 0b101,
            } => {
                register_field!(write self, value, mmu_registers.tpidr2_el0)
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
