// Copyright 2022 Akira Moroo.
// Portions Copyright 2020 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: BSD-3-Clause

use std::{os::unix::net::UnixListener, pin::Pin};

use gdbstub::{
    arch::Arch,
    common::Signal,
    conn::{Connection, ConnectionExt},
    stub::{run_blocking, DisconnectReason, SingleThreadStopReason},
    target::{
        ext::{
            base::{
                single_register_access::{SingleRegisterAccess, SingleRegisterAccessOps},
                singlethread::{
                    SingleThreadBase, SingleThreadResume, SingleThreadResumeOps,
                    SingleThreadSingleStep, SingleThreadSingleStepOps,
                },
                BaseOps,
            },
            breakpoints::{
                Breakpoints, BreakpointsOps, HwBreakpoint, HwBreakpointOps, SwBreakpoint,
                SwBreakpointOps,
            },
            memory_map::{MemoryMap as MemoryMapXML, MemoryMapOps},
        },
        Target, TargetError, TargetResult,
    },
};
use log::{error, info};

use crate::memory::Address;

pub struct GdbStub {
    machine: Pin<Box<crate::machine::Armv8AMachine>>,
    jit_ctx: Pin<Box<crate::jit::JitContext>>,
    entry_func: crate::jit::Entry,
    hw_breakpoints: Vec<Address>,
}

impl GdbStub {
    pub fn new(
        mut machine: Pin<Box<crate::machine::Armv8AMachine>>,
        start_address: crate::memory::Address,
        hw_breakpoints: usize,
    ) -> Self {
        let jit_ctx = crate::jit::JitContext::new();
        if machine.pc == 0 {
            machine.pc = start_address.0;
        }
        let entry_func = machine.lookup_entry_func;
        Self {
            machine,
            jit_ctx,
            entry_func,
            hw_breakpoints: Vec::with_capacity(hw_breakpoints),
        }
    }
}

impl Target for GdbStub {
    type Arch = gdbstub_arch::aarch64::AArch64;
    type Error = String;

    #[inline(always)]
    fn base_ops(&mut self) -> BaseOps<Self::Arch, Self::Error> {
        BaseOps::SingleThread(self)
    }

    #[inline(always)]
    fn support_breakpoints(&mut self) -> Option<BreakpointsOps<Self>> {
        Some(self)
    }

    #[inline(always)]
    fn support_memory_map(&mut self) -> Option<MemoryMapOps<'_, Self>> {
        Some(self)
    }

    #[inline(always)]
    fn guard_rail_implicit_sw_breakpoints(&self) -> bool {
        false
    }
}

impl SingleThreadBase for GdbStub {
    #[inline(always)]
    fn support_single_register_access(&mut self) -> Option<SingleRegisterAccessOps<(), Self>> {
        Some(self)
    }

    #[inline(always)]
    fn read_registers(
        &mut self,
        regs: &mut <Self::Arch as Arch>::Registers,
    ) -> TargetResult<(), Self> {
        macro_rules! read_x {
            ($(($i:literal, $field:ident)),*$(,)*) => {{
                $(
                    regs.x[$i] = self.machine.cpu_state.registers.$field;
                )*
            }};
        }
        read_x! {
            (0, x0),
            (1, x1),
            (2, x2),
            (3, x3),
            (4, x4),
            (5, x5),
            (6, x6),
            (7, x7),
            (8, x8),
            (9, x9),
            (10, x10),
            (11, x11),
            (12, x12),
            (13, x13),
            (14, x14),
            (15, x15),
            (16, x16),
            (17, x17),
            (18, x18),
            (19, x19),
            (20, x20),
            (21, x21),
            (22, x22),
            (23, x23),
            (24, x24),
            (25, x25),
            (26, x26),
            (27, x27),
            (28, x28),
            (29, x29),
            (30, x30),
        }
        regs.sp = self.machine.cpu_state.registers.sp;
        regs.pc = self.machine.pc;
        regs.cpsr = u64::from(self.machine.cpu_state.registers.nzcv) as u32;
        regs.v.fill(0);
        regs.fpcr = 0;
        regs.fpsr = 0;
        Ok(())
    }

    #[inline(always)]
    fn write_registers(
        &mut self,
        _regs: &<Self::Arch as Arch>::Registers,
    ) -> TargetResult<(), Self> {
        error!("Cannot write to guest registers");
        Err(TargetError::NonFatal)
    }

    #[inline(always)]
    fn read_addrs(
        &mut self,
        start_address: <Self::Arch as Arch>::Usize,
        data: &mut [u8],
    ) -> TargetResult<usize, Self> {
        let start_address = Address(start_address);
        info!("reading memory from {}", start_address);
        let Some(mem_region) = self.machine.memory.find_region(start_address) else {
            error!(
                "Cannot read from address {} which is not covered by a RAM memory region.",
                start_address
            );
            return Err(TargetError::NonFatal);
        };
        let address_inside_region = start_address.0 - mem_region.phys_offset.0;
        let Some(mmapped_region) = mem_region.as_mmap() else {
            error!(
                "Cannot read from address {} which is mapped to device memory",
                start_address
            );
            return Err(TargetError::NonFatal);
        };
        let r: &[u8] = &mmapped_region.map.as_ref()[address_inside_region as usize..];
        for (dst, v) in data.iter_mut().zip(r.iter()) {
            *dst = *v;
        }
        Ok(std::cmp::min(data.len(), r.len()))
    }

    #[inline(always)]
    fn write_addrs(
        &mut self,
        _start_addr: <Self::Arch as Arch>::Usize,
        _data: &[u8],
    ) -> TargetResult<(), Self> {
        error!("Cannot write to guest memory",);
        Err(TargetError::NonFatal)
    }

    #[inline(always)]
    fn support_resume(&mut self) -> Option<SingleThreadResumeOps<Self>> {
        Some(self)
    }
}

impl SingleRegisterAccess<()> for GdbStub {
    #[inline(always)]
    fn read_register(
        &mut self,
        _tid: (),
        reg_id: <Self::Arch as Arch>::RegId,
        buf: &mut [u8],
    ) -> TargetResult<usize, Self> {
        use gdbstub_arch::aarch64::reg::id::AArch64RegId;

        if buf.len() < 8 {
            return Err(TargetError::NonFatal);
        }

        macro_rules! read_64bit_reg {
            ($value:expr) => {{
                buf[..8].copy_from_slice(&$value.to_le_bytes());
                Ok(8)
            }};
        }
        match reg_id {
            AArch64RegId::X(0) => read_64bit_reg!(self.machine.cpu_state.registers.x0),
            AArch64RegId::X(1) => read_64bit_reg!(self.machine.cpu_state.registers.x1),
            AArch64RegId::X(2) => read_64bit_reg!(self.machine.cpu_state.registers.x2),
            AArch64RegId::X(3) => read_64bit_reg!(self.machine.cpu_state.registers.x3),
            AArch64RegId::X(4) => read_64bit_reg!(self.machine.cpu_state.registers.x4),
            AArch64RegId::X(5) => read_64bit_reg!(self.machine.cpu_state.registers.x5),
            AArch64RegId::X(6) => read_64bit_reg!(self.machine.cpu_state.registers.x6),
            AArch64RegId::X(7) => read_64bit_reg!(self.machine.cpu_state.registers.x7),
            AArch64RegId::X(8) => read_64bit_reg!(self.machine.cpu_state.registers.x8),
            AArch64RegId::X(9) => read_64bit_reg!(self.machine.cpu_state.registers.x9),
            AArch64RegId::X(10) => read_64bit_reg!(self.machine.cpu_state.registers.x10),
            AArch64RegId::X(11) => read_64bit_reg!(self.machine.cpu_state.registers.x11),
            AArch64RegId::X(12) => read_64bit_reg!(self.machine.cpu_state.registers.x12),
            AArch64RegId::X(13) => read_64bit_reg!(self.machine.cpu_state.registers.x13),
            AArch64RegId::X(14) => read_64bit_reg!(self.machine.cpu_state.registers.x14),
            AArch64RegId::X(15) => read_64bit_reg!(self.machine.cpu_state.registers.x15),
            AArch64RegId::X(16) => read_64bit_reg!(self.machine.cpu_state.registers.x16),
            AArch64RegId::X(17) => read_64bit_reg!(self.machine.cpu_state.registers.x17),
            AArch64RegId::X(18) => read_64bit_reg!(self.machine.cpu_state.registers.x18),
            AArch64RegId::X(19) => read_64bit_reg!(self.machine.cpu_state.registers.x19),
            AArch64RegId::X(20) => read_64bit_reg!(self.machine.cpu_state.registers.x20),
            AArch64RegId::X(21) => read_64bit_reg!(self.machine.cpu_state.registers.x21),
            AArch64RegId::X(22) => read_64bit_reg!(self.machine.cpu_state.registers.x22),
            AArch64RegId::X(23) => read_64bit_reg!(self.machine.cpu_state.registers.x23),
            AArch64RegId::X(24) => read_64bit_reg!(self.machine.cpu_state.registers.x24),
            AArch64RegId::X(25) => read_64bit_reg!(self.machine.cpu_state.registers.x25),
            AArch64RegId::X(26) => read_64bit_reg!(self.machine.cpu_state.registers.x26),
            AArch64RegId::X(27) => read_64bit_reg!(self.machine.cpu_state.registers.x27),
            AArch64RegId::X(28) => read_64bit_reg!(self.machine.cpu_state.registers.x28),
            AArch64RegId::X(29) => read_64bit_reg!(self.machine.cpu_state.registers.x29),
            AArch64RegId::X(30) => read_64bit_reg!(self.machine.cpu_state.registers.x30),
            AArch64RegId::X(other) => {
                error!("GDB requested read of invalid register x{other}");
                Err(TargetError::NonFatal)
            }
            AArch64RegId::Sp => read_64bit_reg!(self.machine.cpu_state.registers.sp),
            AArch64RegId::Pc => read_64bit_reg!(self.machine.pc),
            AArch64RegId::Pstate => {
                read_64bit_reg!(u64::from(self.machine.cpu_state.registers.nzcv))
            }
            AArch64RegId::V(_) => {
                buf[..16].fill(0);
                Ok(16)
            }
            AArch64RegId::SP_EL0 => read_64bit_reg!(self.machine.cpu_state.registers.sp_el0),
            AArch64RegId::SP_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.sp_el1),
            AArch64RegId::SP_EL2 => read_64bit_reg!(self.machine.cpu_state.registers.sp_el2),
            // AArch64RegId::SP_EL3 => read_64bit_reg!(self.machine.cpu_state.registers.sp_el3),
            AArch64RegId::TTBR0_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.ttbr0_el1),
            AArch64RegId::VTTBR_EL2 => read_64bit_reg!(self.machine.cpu_state.registers.vttbr_el2),
            AArch64RegId::MAIR_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.mair_el1),
            AArch64RegId::TCR_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.tcr_el1),
            AArch64RegId::SCTLR_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.sctlr_el1),
            AArch64RegId::SCTLR_EL2 => read_64bit_reg!(self.machine.cpu_state.registers.sctlr_el2),
            AArch64RegId::SCTLR_EL3 => read_64bit_reg!(self.machine.cpu_state.registers.sctlr_el3),
            AArch64RegId::CPACR_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.cpacr_el1),
            AArch64RegId::VBAR_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.vbar_el1),
            AArch64RegId::HCR_EL2 => read_64bit_reg!(self.machine.cpu_state.registers.hcr_el2),
            AArch64RegId::SCR_EL3 => read_64bit_reg!(self.machine.cpu_state.registers.scr_el3),
            AArch64RegId::VPIDR_EL2 => read_64bit_reg!(self.machine.cpu_state.registers.vpidr_el2),
            AArch64RegId::VMPIDR_EL2 => {
                read_64bit_reg!(self.machine.cpu_state.registers.vmpidr_el2)
            }
            AArch64RegId::SPSR_EL3 => {
                read_64bit_reg!(u64::from(self.machine.cpu_state.registers.spsr_el3))
            }
            AArch64RegId::ELR_EL1 => read_64bit_reg!(self.machine.cpu_state.registers.elr_el1),
            AArch64RegId::ELR_EL2 => read_64bit_reg!(self.machine.cpu_state.registers.elr_el2),
            AArch64RegId::ELR_EL3 => read_64bit_reg!(self.machine.cpu_state.registers.elr_el3),
            // AArch64RegId::OSDTRRX_EL1 => Ok(0),
            // AArch64RegId::DBGBVR0_EL1 => Ok(0),
            // AArch64RegId::DBGBCR0_EL1 => Ok(0),
            // AArch64RegId::DBGWVR0_EL1 => Ok(0),
            // AArch64RegId::DBGWCR0_EL1 => Ok(0),
            _ => Ok(0),
        }
    }

    #[inline(always)]
    fn write_register(
        &mut self,
        _tid: (),
        reg_id: <Self::Arch as Arch>::RegId,
        val: &[u8],
    ) -> TargetResult<(), Self> {
        use gdbstub_arch::aarch64::reg::id::AArch64RegId;

        let Some(val_64): Option<[u8; 8]> =
            val.get(..8).and_then(|val| <[u8; 8]>::try_from(val).ok())
        else {
            return Err(TargetError::NonFatal);
        };

        macro_rules! write_64bit_reg {
            ($dest:expr) => {{
                $dest = u64::from_ne_bytes(val_64);
            }};
        }
        match reg_id {
            AArch64RegId::X(0) => write_64bit_reg!(self.machine.cpu_state.registers.x0),
            AArch64RegId::X(1) => write_64bit_reg!(self.machine.cpu_state.registers.x1),
            AArch64RegId::X(2) => write_64bit_reg!(self.machine.cpu_state.registers.x2),
            AArch64RegId::X(3) => write_64bit_reg!(self.machine.cpu_state.registers.x3),
            AArch64RegId::X(4) => write_64bit_reg!(self.machine.cpu_state.registers.x4),
            AArch64RegId::X(5) => write_64bit_reg!(self.machine.cpu_state.registers.x5),
            AArch64RegId::X(6) => write_64bit_reg!(self.machine.cpu_state.registers.x6),
            AArch64RegId::X(7) => write_64bit_reg!(self.machine.cpu_state.registers.x7),
            AArch64RegId::X(8) => write_64bit_reg!(self.machine.cpu_state.registers.x8),
            AArch64RegId::X(9) => write_64bit_reg!(self.machine.cpu_state.registers.x9),
            AArch64RegId::X(10) => write_64bit_reg!(self.machine.cpu_state.registers.x10),
            AArch64RegId::X(11) => write_64bit_reg!(self.machine.cpu_state.registers.x11),
            AArch64RegId::X(12) => write_64bit_reg!(self.machine.cpu_state.registers.x12),
            AArch64RegId::X(13) => write_64bit_reg!(self.machine.cpu_state.registers.x13),
            AArch64RegId::X(14) => write_64bit_reg!(self.machine.cpu_state.registers.x14),
            AArch64RegId::X(15) => write_64bit_reg!(self.machine.cpu_state.registers.x15),
            AArch64RegId::X(16) => write_64bit_reg!(self.machine.cpu_state.registers.x16),
            AArch64RegId::X(17) => write_64bit_reg!(self.machine.cpu_state.registers.x17),
            AArch64RegId::X(18) => write_64bit_reg!(self.machine.cpu_state.registers.x18),
            AArch64RegId::X(19) => write_64bit_reg!(self.machine.cpu_state.registers.x19),
            AArch64RegId::X(20) => write_64bit_reg!(self.machine.cpu_state.registers.x20),
            AArch64RegId::X(21) => write_64bit_reg!(self.machine.cpu_state.registers.x21),
            AArch64RegId::X(22) => write_64bit_reg!(self.machine.cpu_state.registers.x22),
            AArch64RegId::X(23) => write_64bit_reg!(self.machine.cpu_state.registers.x23),
            AArch64RegId::X(24) => write_64bit_reg!(self.machine.cpu_state.registers.x24),
            AArch64RegId::X(25) => write_64bit_reg!(self.machine.cpu_state.registers.x25),
            AArch64RegId::X(26) => write_64bit_reg!(self.machine.cpu_state.registers.x26),
            AArch64RegId::X(27) => write_64bit_reg!(self.machine.cpu_state.registers.x27),
            AArch64RegId::X(28) => write_64bit_reg!(self.machine.cpu_state.registers.x28),
            AArch64RegId::X(29) => write_64bit_reg!(self.machine.cpu_state.registers.x29),
            AArch64RegId::X(30) => write_64bit_reg!(self.machine.cpu_state.registers.x30),
            AArch64RegId::X(other) => {
                error!("GDB requested write of invalid register x{other}");
                return Err(TargetError::NonFatal);
            }
            AArch64RegId::Sp => write_64bit_reg!(self.machine.cpu_state.registers.sp),
            AArch64RegId::Pc => write_64bit_reg!(self.machine.pc),
            AArch64RegId::Pstate => {
                self.machine.cpu_state.registers.nzcv = u64::from_ne_bytes(val_64).into();
            }
            AArch64RegId::V(_) => {
                // FIXME
                unimplemented!()
            }
            AArch64RegId::SP_EL0 => write_64bit_reg!(self.machine.cpu_state.registers.sp_el0),
            AArch64RegId::SP_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.sp_el1),
            AArch64RegId::SP_EL2 => write_64bit_reg!(self.machine.cpu_state.registers.sp_el2),
            // AArch64RegId::SP_EL3 => write_64bit_reg!(self.machine.cpu_state.registers.sp_el3),
            AArch64RegId::TTBR0_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.ttbr0_el1),
            AArch64RegId::VTTBR_EL2 => write_64bit_reg!(self.machine.cpu_state.registers.vttbr_el2),
            AArch64RegId::MAIR_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.mair_el1),
            AArch64RegId::TCR_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.tcr_el1),
            AArch64RegId::SCTLR_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.sctlr_el1),
            AArch64RegId::SCTLR_EL2 => write_64bit_reg!(self.machine.cpu_state.registers.sctlr_el2),
            AArch64RegId::SCTLR_EL3 => write_64bit_reg!(self.machine.cpu_state.registers.sctlr_el3),
            AArch64RegId::CPACR_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.cpacr_el1),
            AArch64RegId::VBAR_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.vbar_el1),
            AArch64RegId::HCR_EL2 => write_64bit_reg!(self.machine.cpu_state.registers.hcr_el2),
            AArch64RegId::SCR_EL3 => write_64bit_reg!(self.machine.cpu_state.registers.scr_el3),
            AArch64RegId::VPIDR_EL2 => write_64bit_reg!(self.machine.cpu_state.registers.vpidr_el2),
            AArch64RegId::VMPIDR_EL2 => {
                write_64bit_reg!(self.machine.cpu_state.registers.vmpidr_el2)
            }
            AArch64RegId::SPSR_EL3 => {
                self.machine.cpu_state.registers.spsr_el3 = u64::from_ne_bytes(val_64).into();
            }
            AArch64RegId::ELR_EL1 => write_64bit_reg!(self.machine.cpu_state.registers.elr_el1),
            AArch64RegId::ELR_EL2 => write_64bit_reg!(self.machine.cpu_state.registers.elr_el2),
            AArch64RegId::ELR_EL3 => write_64bit_reg!(self.machine.cpu_state.registers.elr_el3),
            _ => return Err(TargetError::NonFatal),
        }
        Ok(())
    }
}

impl SingleThreadResume for GdbStub {
    #[inline(always)]
    fn resume(&mut self, _signal: Option<Signal>) -> Result<(), Self::Error> {
        self.jit_ctx.single_step = true;
        Ok(())
    }

    #[inline(always)]
    fn support_single_step(&mut self) -> Option<SingleThreadSingleStepOps<'_, Self>> {
        Some(self)
    }
}

impl SingleThreadSingleStep for GdbStub {
    #[inline(always)]
    fn step(&mut self, _signal: Option<Signal>) -> Result<(), Self::Error> {
        info!("step called");
        self.jit_ctx.single_step = true;
        Ok(())
    }
}

impl Breakpoints for GdbStub {
    #[inline(always)]
    fn support_sw_breakpoint(&mut self) -> Option<SwBreakpointOps<Self>> {
        Some(self)
    }

    #[inline(always)]
    fn support_hw_breakpoint(&mut self) -> Option<HwBreakpointOps<Self>> {
        Some(self)
    }
}

impl SwBreakpoint for GdbStub {
    #[inline(always)]
    fn add_sw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        // If the HW breakpoints reach the limit, no more can be added.
        if self.hw_breakpoints.len() >= self.hw_breakpoints.capacity() {
            error!(
                "Not allowed to set more than {} HW breakpoints",
                self.hw_breakpoints.capacity()
            );
            return Ok(false);
        }

        self.hw_breakpoints.push(Address(addr));

        Ok(true)
    }

    #[inline(always)]
    fn remove_sw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        match self.hw_breakpoints.iter().position(|&b| b.0 == addr) {
            None => return Ok(false),
            Some(pos) => self.hw_breakpoints.remove(pos),
        };
        Ok(true)
    }
}

impl HwBreakpoint for GdbStub {
    #[inline(always)]
    fn add_hw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        // If the HW breakpoints reach the limit, no more can be added.
        if self.hw_breakpoints.len() >= self.hw_breakpoints.capacity() {
            error!(
                "Not allowed to set more than {} HW breakpoints",
                self.hw_breakpoints.capacity()
            );
            return Ok(false);
        }

        self.hw_breakpoints.push(Address(addr));

        Ok(true)
    }

    #[inline(always)]
    fn remove_hw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        match self.hw_breakpoints.iter().position(|&b| b.0 == addr) {
            None => return Ok(false),
            Some(pos) => self.hw_breakpoints.remove(pos),
        };
        Ok(true)
    }
}

impl MemoryMapXML for GdbStub {
    fn memory_map_xml(
        &self,
        offset: u64,
        length: usize,
        buf: &mut [u8],
    ) -> TargetResult<usize, Self> {
        let mut memory_entries = String::new();
        for (mmap, region) in self
            .machine
            .memory
            .iter()
            .filter_map(|r| Some((r.as_mmap()?, r)))
        {
            use std::fmt::Write;

            writeln!(
                &mut memory_entries,
                "<memory type=\"{type}\" start=\"0x{start:x}\" length=\"0x{length:x}\"/>#",
                r#type = if mmap.read_only { "rom" } else { "ram" },
                start = region.start_addr().0,
                length = (region.last_addr() - region.start_addr()).0,
            )
            .map_err(|_| TargetError::Errno(nix::errno::Errno::ENOMEM as u8))?;
        }
        let memory_map = format!(
            r#"<?xml version="1.0"?>
<!DOCTYPE memory-map
    PUBLIC "+//IDN gnu.org//DTD GDB Memory Map V1.0//EN"
            "http://sourceware.org/gdb/gdb-memory-map.dtd">
<memory-map>
    {memory_entries}</memory-map>"#
        );

        let offset = offset as usize;
        if offset > memory_map.len() {
            return Ok(0);
        }

        let start = offset;
        let end = (offset + length).min(memory_map.len());
        let data = &memory_map.as_bytes()[start..end];
        let len = buf.len().min(data.len());
        buf[..len].copy_from_slice(&data[..len]);
        Ok(len)
    }
}

enum GdbEventLoop {}

type ArchUsize = u64;

impl run_blocking::BlockingEventLoop for GdbEventLoop {
    type Target = GdbStub;
    type Connection = Box<dyn ConnectionExt<Error = std::io::Error>>;
    type StopReason = SingleThreadStopReason<ArchUsize>;

    fn wait_for_stop_reason(
        target: &mut Self::Target,
        conn: &mut Self::Connection,
    ) -> Result<
        run_blocking::Event<Self::StopReason>,
        run_blocking::WaitForStopReasonError<
            <Self::Target as Target>::Error,
            <Self::Connection as Connection>::Error,
        >,
    > {
        while target.machine.halted == 0 {
            if conn.peek().map(|b| b.is_some()).unwrap_or(true) {
                let byte = conn
                    .read()
                    .map_err(run_blocking::WaitForStopReasonError::Connection)?;
                return Ok(run_blocking::Event::IncomingData(byte));
            }
            let func = target.entry_func;
            target.entry_func = (func.0)(&mut target.jit_ctx, &mut target.machine);
            if target.jit_ctx.single_step {
                return Ok(run_blocking::Event::TargetStopped(
                    SingleThreadStopReason::DoneStep,
                ));
            }
            //         } else {
            //             SingleThreadStopReason::HwBreak(Tid::new(tid as
            // usize).unwrap())         };
        }
        Ok(run_blocking::Event::TargetStopped(
            SingleThreadStopReason::Exited(0),
        ))
    }

    fn on_interrupt(
        _target: &mut Self::Target,
    ) -> Result<Option<Self::StopReason>, <Self::Target as Target>::Error> {
        Ok(Some(SingleThreadStopReason::Signal(Signal::SIGINT)))
    }
}

pub fn main_loop(mut gdbstub: GdbStub, path: &std::path::Path) {
    let listener = match UnixListener::bind(path) {
        Ok(s) => s,
        Err(e) => {
            error!("Failed to create a Unix domain socket listener: {}", e);
            return;
        }
    };
    info!("Waiting for a GDB connection on {}...", path.display());

    let (stream, addr) = match listener.accept() {
        Ok(v) => v,
        Err(e) => {
            error!("Failed to accept a connection from GDB: {}", e);
            return;
        }
    };
    info!("GDB connected from {:?}", addr);

    let connection: Box<dyn ConnectionExt<Error = std::io::Error>> = Box::new(stream);
    let gdb = gdbstub::stub::GdbStub::new(connection);

    match gdb.run_blocking::<GdbEventLoop>(&mut gdbstub) {
        Ok(disconnect_reason) => match disconnect_reason {
            DisconnectReason::Disconnect => {
                info!("GDB client has disconnected. Exiting...");
            }
            other => {
                error!("Target exited or terminated: {:?}", other);
            }
        },
        Err(e) => {
            error!("error occurred in GDB session: {}", e);
        }
    }
    _ = std::fs::remove_file(path);
}
