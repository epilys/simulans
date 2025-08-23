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

use std::{
    os::unix::net::UnixListener,
    pin::Pin,
    sync::{
        mpsc::{channel, sync_channel, Receiver, Sender, SyncSender},
        Arc, Condvar, Mutex,
    },
};

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
            monitor_cmd::{ConsoleOutput, MonitorCmd, MonitorCmdOps},
        },
        Target, TargetError, TargetResult,
    },
};
use log::{error, info};

use crate::memory::Address;

/// Helper struct for memory map xml
struct GdbMemoryMap {
    read_only: bool,
    start: u64,
    length: u64,
}

enum GdbStubRequest<A: Arch> {
    ReadRegs(SyncSender<<A as Arch>::Registers>),
    WriteRegs(<A as Arch>::Registers),
    ReadReg(
        <A as Arch>::RegId,
        SyncSender<TargetResult<Box<[u8]>, GdbStub>>,
    ),
    WriteReg(<A as Arch>::RegId, Box<[u8]>),
    ReadAddrs(
        <A as Arch>::Usize,
        usize,
        SyncSender<TargetResult<Box<[u8]>, GdbStub>>,
    ),
    WriteAddrs(<A as Arch>::Usize, Box<[u8]>),
    AddBreakpoint(<A as Arch>::Usize),
    DelBreakpoint(<A as Arch>::Usize, SyncSender<bool>),
    MonitorCommand(String, SyncSender<String>),
    Interrupt,
    Resume,
    SingleStep,
    MemoryMaps(SyncSender<Vec<GdbMemoryMap>>),
    //Reset,
}

impl std::fmt::Debug for GdbStubRequest<AArch64> {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Self::ReadRegs(_) => fmt
                .debug_tuple("GdbStubRequest::ReadRegs")
                .finish_non_exhaustive(),
            Self::WriteRegs(_) => fmt
                .debug_tuple("GdbStubRequest::WriteRegs")
                .finish_non_exhaustive(),
            Self::ReadReg(ref reg_id, _) => fmt
                .debug_tuple("GdbStubRequest::ReadReg")
                .field(reg_id)
                .finish_non_exhaustive(),
            Self::WriteReg(ref reg_id, _) => fmt
                .debug_tuple("GdbStubRequest::WriteReg")
                .field(reg_id)
                .finish_non_exhaustive(),
            Self::ReadAddrs(ref addr, ref max_bytes, _) => fmt
                .debug_tuple("GdbStubRequest::ReadAddrs")
                .field(addr)
                .field(max_bytes)
                .finish_non_exhaustive(),
            Self::WriteAddrs(ref addr, ref value) => fmt
                .debug_tuple("GdbStubRequest::WriteAddrs")
                .field(addr)
                .field(&value.len())
                .finish_non_exhaustive(),
            Self::AddBreakpoint(ref addr) => fmt
                .debug_tuple("GdbStubRequest::AddBreakpoint")
                .field(addr)
                .finish_non_exhaustive(),
            Self::DelBreakpoint(ref addr, _) => fmt
                .debug_tuple("GdbStubRequest::DelBreakpoint")
                .field(addr)
                .finish_non_exhaustive(),
            Self::MonitorCommand(ref s, _) => fmt
                .debug_tuple("GdbStubRequest::")
                .field(s)
                .finish_non_exhaustive(),
            Self::Interrupt => fmt.debug_tuple("GdbStubRequest::Interrupt").finish(),
            Self::Resume => fmt.debug_tuple("GdbStubRequest::Resume").finish(),
            Self::SingleStep => fmt.debug_tuple("GdbStubRequest::SingleStep").finish(),
            Self::MemoryMaps(..) => fmt.debug_tuple("GdbStubRequest::MemoryMaps").finish(),
        }
    }
}

pub struct GdbStubRunner {
    request_receiver: Receiver<GdbStubRequest<AArch64>>,
    request_complete_signal: Arc<(Mutex<bool>, Condvar)>,
    stop_sender: SyncSender<SingleThreadStopReason<<AArch64 as Arch>::Usize>>,
    machine: Pin<Box<crate::machine::Armv8AMachine>>,
    jit_ctx: Pin<Box<crate::jit::JitContext>>,
}

type AArch64 = gdbstub_arch::aarch64::AArch64;

impl GdbStubRunner {
    #[inline(always)]
    fn read_registers(&self, regs: &mut <AArch64 as Arch>::Registers) {
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
    }

    #[inline(always)]
    fn write_registers(&mut self, regs: <AArch64 as Arch>::Registers) {
        macro_rules! write_x {
            ($(($i:literal, $field:ident)),*$(,)*) => {{
                $(
                    self.machine.cpu_state.registers.$field = regs.x[$i];
                )*
            }};
        }
        write_x! {
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
        self.machine.cpu_state.registers.sp = regs.sp;
        self.machine.pc = regs.pc;
        self.machine.cpu_state.registers.nzcv = u64::from(regs.cpsr).into();
    }

    #[inline(always)]
    fn read_addrs(
        &self,
        start_address: <AArch64 as Arch>::Usize,
        max_bytes: usize,
    ) -> TargetResult<Box<[u8]>, GdbStub> {
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
        let r: &[u8] = &mmapped_region.as_ref()[address_inside_region as usize..];
        let r = &r[..max_bytes.min(r.len())];
        Ok(r.into())
    }

    #[inline(always)]
    fn write_addrs(
        &mut self,
        start_address: <AArch64 as Arch>::Usize,
        value: &[u8],
    ) -> TargetResult<(), GdbStub> {
        let start_address = Address(start_address);
        info!("reading memory from {}", start_address);
        let Some(mem_region) = self.machine.memory.find_region_mut(start_address) else {
            error!(
                "Cannot read from address {} which is not covered by a RAM memory region.",
                start_address
            );
            return Err(TargetError::NonFatal);
        };
        let address_inside_region = start_address.0 - mem_region.phys_offset.0;
        let Some(mmapped_region) = mem_region.as_mmap_mut() else {
            error!(
                "Cannot read from address {} which is mapped to device memory",
                start_address
            );
            return Err(TargetError::NonFatal);
        };
        let r: &mut [u8] = &mut mmapped_region.as_mut()[address_inside_region as usize..];
        let max_len = value.len().min(r.len());
        let r = &mut r[..max_len];
        for (dst, v) in r.iter_mut().zip(value.iter()) {
            *dst = *v;
        }
        Ok(())
    }

    #[inline(always)]
    fn read_register(&self, reg_id: <AArch64 as Arch>::RegId) -> TargetResult<Box<[u8]>, GdbStub> {
        use gdbstub_arch::aarch64::reg::id::AArch64RegId;

        macro_rules! read_64bit_reg {
            ($value:expr) => {{
                Ok($value.to_le_bytes().into())
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
            AArch64RegId::V(_) => Ok(Box::new([0; 16])),
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
            _ => Ok(Box::new([0; 0])),
        }
    }

    #[inline(always)]
    fn write_register(
        &mut self,
        reg_id: <AArch64 as Arch>::RegId,
        val: &[u8],
    ) -> TargetResult<(), GdbStub> {
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

    #[inline(always)]
    fn handle_monitor_cmd(&self, s: &str) -> String {
        let words = s.split_whitespace().collect::<Vec<&str>>();
        if words.is_empty() {
            return String::from("Available monitor commands: {{log,pc,state,registers}}");
        }

        match words[0] {
            "log" => match words.get(1) {
                None => {
                    return format!(
                        "Log level is {:?}. Available levels: {{trace,debug,error,warn,info,off}}",
                        log::max_level()
                    )
                }
                Some(trace) if trace.eq_ignore_ascii_case("trace") => {
                    log::set_max_level(log::LevelFilter::Trace);
                }
                Some(debug) if debug.eq_ignore_ascii_case("debug") => {
                    log::set_max_level(log::LevelFilter::Debug);
                }
                Some(error) if error.eq_ignore_ascii_case("error") => {
                    log::set_max_level(log::LevelFilter::Error);
                }
                Some(info) if info.eq_ignore_ascii_case("info") => {
                    log::set_max_level(log::LevelFilter::Info);
                }
                Some(warn) if warn.eq_ignore_ascii_case("warn") => {
                    log::set_max_level(log::LevelFilter::Warn);
                }
                Some(off) if off.eq_ignore_ascii_case("off") => {
                    log::set_max_level(log::LevelFilter::Off);
                }
                Some(other) => {
                    return format!(
                        "Invalid log level {other:?}: valid log level values: \
                         {{trace,debug,error,warn,info,off}}"
                    );
                }
            },
            "pc" => {
                return format!(
                    "Pc = 0x{:x}\nPrev Pc = 0x{:x}",
                    self.machine.pc, self.machine.prev_pc
                );
            }
            "state" => {
                return format!("{:?}", self.machine.cpu_state);
            }
            "registers" => {
                return format!("{:?}", self.machine.cpu_state.registers);
            }
            other => {
                return format!(
                    "Unexpected command {other:?}: available commands: {{log,pc,state,registers}}"
                );
            }
        }

        String::new()
    }

    #[inline(always)]
    fn add_breakpoint(&mut self, addr: <AArch64 as Arch>::Usize) {
        debug_assert!(
            addr.rem_euclid(4) == 0,
            "Adding unaligned breakpoint addr 0x{:x}",
            addr
        );
        self.machine.hw_breakpoints.insert(Address(addr));
        self.machine.entry_blocks.invalidate(addr);
    }

    #[inline(always)]
    fn remove_breakpoint(&mut self, addr: <AArch64 as Arch>::Usize) -> bool {
        debug_assert!(
            addr.rem_euclid(4) == 0,
            "Removing unaligned breakpoint addr 0x{:x}",
            addr
        );
        if !self.machine.hw_breakpoints.remove(&Address(addr)) {
            return false;
        }
        self.machine.entry_blocks.invalidate(addr);
        true
    }

    fn run(&mut self) {
        #[derive(Copy, Clone)]
        #[repr(u8)]
        enum State {
            Running,
            Stopped,
        }
        fn handle_request(
            self_: &mut GdbStubRunner,
            request: GdbStubRequest<AArch64>,
        ) -> Option<State> {
            match request {
                GdbStubRequest::ReadRegs(sender) => {
                    let mut regs = Default::default();
                    self_.read_registers(&mut regs);
                    sender.send(regs).unwrap();
                }
                GdbStubRequest::WriteRegs(regs) => {
                    self_.write_registers(regs);
                }
                GdbStubRequest::ReadReg(reg_id, sender) => {
                    let res = self_.read_register(reg_id);
                    sender.send(res).unwrap();
                }
                GdbStubRequest::WriteReg(reg_id, value) => {
                    _ = self_.write_register(reg_id, &value);
                }
                GdbStubRequest::ReadAddrs(addr, max_bytes, sender) => {
                    let res = self_.read_addrs(addr, max_bytes);
                    sender.send(res).unwrap();
                }
                GdbStubRequest::WriteAddrs(addr, value) => {
                    _ = self_.write_addrs(addr, &value);
                }
                GdbStubRequest::AddBreakpoint(addr) => {
                    self_.add_breakpoint(addr);
                }
                GdbStubRequest::DelBreakpoint(addr, sender) => {
                    let res = self_.remove_breakpoint(addr);
                    sender.send(res).unwrap();
                }
                GdbStubRequest::MonitorCommand(s, sender) => {
                    let response = self_.handle_monitor_cmd(&s);
                    sender.send(response).unwrap();
                }
                GdbStubRequest::Interrupt => {
                    return Some(State::Stopped);
                }
                GdbStubRequest::Resume => {
                    return Some(State::Running);
                }
                GdbStubRequest::SingleStep => {
                    self_.jit_ctx.single_step = true;
                    let pc = self_.machine.pc;
                    self_.machine.entry_blocks.invalidate(pc);
                    let entry = crate::jit::lookup_entry(&mut self_.jit_ctx, &mut self_.machine);
                    (entry.0)(&mut self_.jit_ctx, &mut self_.machine);
                    // self_.jit_ctx.single_step = false;
                    self_
                        .stop_sender
                        .send(SingleThreadStopReason::DoneStep)
                        .unwrap();
                    return Some(State::Stopped);
                }
                GdbStubRequest::MemoryMaps(sender) => {
                    let mut entries = vec![];
                    for (mmap, region) in self_
                        .machine
                        .memory
                        .iter()
                        .filter_map(|r| Some((r.as_mmap()?, r)))
                    {
                        entries.push(GdbMemoryMap {
                            read_only: mmap.read_only,
                            start: region.start_addr().0,
                            length: (region.last_addr() - region.start_addr()).0,
                        });
                    }
                    sender.send(entries).unwrap();
                }
            }
            None
        }

        let mut state = State::Stopped;
        'main_loop: loop {
            if let Ok(request) = self.request_receiver.try_recv() {
                if let Some(new_state) = handle_request(self, request) {
                    state = new_state;
                }
                self.ack();
            }
            match state {
                State::Running => {
                    while self.machine.halted == 0 {
                        if let Ok(request) = self.request_receiver.try_recv() {
                            if let Some(new_state) = handle_request(self, request) {
                                state = new_state;
                                self.ack();
                                continue 'main_loop;
                            }
                            self.ack();
                        }
                        if self.jit_ctx.single_step {
                            let pc = self.machine.pc;
                            self.machine.entry_blocks.invalidate(pc);
                        }
                        if self
                            .machine
                            .hw_breakpoints
                            .contains(&Address(self.machine.pc))
                        {
                            if self.machine.in_breakpoint {
                                // Continue execution after stopping at breakpoint.
                                self.machine.in_breakpoint = false;
                            } else {
                                let pc = self.machine.pc;
                                self.machine.in_breakpoint = true;
                                self.machine.entry_blocks.invalidate(pc);
                                self.stop_sender
                                    .send(SingleThreadStopReason::HwBreak(()))
                                    .unwrap();
                                state = State::Stopped;
                                continue 'main_loop;
                            }
                        }
                        let entry = crate::jit::lookup_entry(&mut self.jit_ctx, &mut self.machine);
                        (entry.0)(&mut self.jit_ctx, &mut self.machine);
                        if self.jit_ctx.single_step {
                            // self.jit_ctx.single_step = false;
                            self.stop_sender
                                .send(SingleThreadStopReason::DoneStep)
                                .unwrap();
                            state = State::Stopped;
                            continue 'main_loop;
                        }
                        if self
                            .machine
                            .hw_breakpoints
                            .contains(&Address(self.machine.pc))
                        {
                            let pc = self.machine.pc;
                            self.machine.in_breakpoint = true;
                            self.machine.entry_blocks.invalidate(pc);
                            self.stop_sender
                                .send(SingleThreadStopReason::HwBreak(()))
                                .unwrap();
                            state = State::Stopped;
                            continue 'main_loop;
                        }
                    }
                    self.stop_sender
                        .send(SingleThreadStopReason::Exited(0))
                        .unwrap();
                    break 'main_loop;
                }
                State::Stopped => {
                    let Ok(request) = self.request_receiver.recv() else {
                        // Gdb has exited.
                        break 'main_loop;
                    };
                    if let Some(new_state) = handle_request(self, request) {
                        state = new_state;
                    }
                    self.ack();
                }
            }
        }
    }

    #[inline(always)]
    fn ack(&self) {
        let (lock, cvar) = &*self.request_complete_signal;
        let mut finished = lock.lock().unwrap();
        *finished = true;
        cvar.notify_one();
        // wait for the ack
        while *finished {
            finished = cvar.wait(finished).unwrap();
        }
        drop(finished);
    }
}

pub struct GdbStub {
    request_sender: Sender<GdbStubRequest<AArch64>>,
    request_complete_signal: Arc<(Mutex<bool>, Condvar)>,
    stop_receiver: Receiver<SingleThreadStopReason<<AArch64 as Arch>::Usize>>,
}

impl GdbStub {
    pub fn new(
        mut machine: Pin<Box<crate::machine::Armv8AMachine>>,
        start_address: crate::memory::Address,
    ) -> Self {
        if machine.pc == 0 {
            machine.pc = start_address.0;
        }
        let request_complete_signal = Arc::new((Mutex::new(false), Condvar::new()));
        let (request_sender, request_receiver) = channel();
        let (stop_sender, stop_receiver) = sync_channel(1);
        std::thread::spawn({
            let request_complete_signal = Arc::clone(&request_complete_signal);
            move || {
                let jit_ctx = crate::jit::JitContext::new();
                let mut runner = GdbStubRunner {
                    request_receiver,
                    request_complete_signal,
                    stop_sender,
                    machine,
                    jit_ctx,
                };
                runner.run();
            }
        });
        Self {
            request_sender,
            request_complete_signal,
            stop_receiver,
        }
    }

    #[inline(always)]
    fn send_request(&self, request: GdbStubRequest<AArch64>) {
        let (lock, cvar) = &*self.request_complete_signal;
        {
            let mut finished = lock.lock().unwrap();
            // now send the request
            self.request_sender.send(request).unwrap();
            // wait for the notification
            while !*finished {
                finished = cvar.wait(finished).unwrap();
            }
            // ack the other side we got the signal
            *finished = false;
        }
        cvar.notify_one();
    }
}

impl Target for GdbStub {
    type Arch = gdbstub_arch::aarch64::AArch64;
    type Error = String;

    #[inline(always)]
    fn base_ops(&mut self) -> BaseOps<'_, Self::Arch, Self::Error> {
        BaseOps::SingleThread(self)
    }

    #[inline(always)]
    fn support_breakpoints(&mut self) -> Option<BreakpointsOps<'_, Self>> {
        Some(self)
    }

    #[inline(always)]
    fn support_monitor_cmd(&mut self) -> Option<MonitorCmdOps<'_, Self>> {
        Some(self)
    }

    #[inline(always)]
    fn support_memory_map(&mut self) -> Option<MemoryMapOps<'_, Self>> {
        //Some(self)
        None
    }

    #[inline(always)]
    fn guard_rail_implicit_sw_breakpoints(&self) -> bool {
        false
    }
}

impl SingleThreadBase for GdbStub {
    #[inline(always)]
    fn support_single_register_access(&mut self) -> Option<SingleRegisterAccessOps<'_, (), Self>> {
        Some(self)
    }

    #[inline(always)]
    fn read_registers(
        &mut self,
        regs: &mut <Self::Arch as Arch>::Registers,
    ) -> TargetResult<(), Self> {
        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::ReadRegs(sender));
        *regs = recv.recv().unwrap();
        Ok(())
    }

    #[inline(always)]
    fn write_registers(
        &mut self,
        regs: &<Self::Arch as Arch>::Registers,
    ) -> TargetResult<(), Self> {
        self.send_request(GdbStubRequest::WriteRegs(regs.clone()));
        Ok(())
    }

    #[inline(always)]
    fn read_addrs(
        &mut self,
        start_address: <Self::Arch as Arch>::Usize,
        data: &mut [u8],
    ) -> TargetResult<usize, Self> {
        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::ReadAddrs(start_address, data.len(), sender));
        let r: Box<[u8]> = recv.recv().unwrap()?;
        for (dst, v) in data.iter_mut().zip(r.iter()) {
            *dst = *v;
        }
        Ok(std::cmp::min(data.len(), r.len()))
    }

    #[inline(always)]
    fn write_addrs(
        &mut self,
        start_addr: <Self::Arch as Arch>::Usize,
        data: &[u8],
    ) -> TargetResult<(), Self> {
        // FIXME: get result back
        self.send_request(GdbStubRequest::WriteAddrs(start_addr, data.into()));
        Ok(())
    }

    #[inline(always)]
    fn support_resume(&mut self) -> Option<SingleThreadResumeOps<'_, Self>> {
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
        if buf.len() < 8 {
            return Err(TargetError::NonFatal);
        }

        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::ReadReg(reg_id, sender));
        let value = recv.recv().unwrap()?;
        for (dst, v) in buf.iter_mut().zip(value.iter()) {
            *dst = *v;
        }
        Ok(std::cmp::min(buf.len(), value.len()))
    }

    #[inline(always)]
    fn write_register(
        &mut self,
        _tid: (),
        reg_id: <Self::Arch as Arch>::RegId,
        val: &[u8],
    ) -> TargetResult<(), Self> {
        if val.len() < 4 {
            return Err(TargetError::NonFatal);
        }

        self.send_request(GdbStubRequest::WriteReg(reg_id, val.into()));
        Ok(())
    }
}

impl SingleThreadResume for GdbStub {
    #[inline(always)]
    fn resume(&mut self, _signal: Option<Signal>) -> Result<(), Self::Error> {
        info!("resume/continue called");
        // self.jit_ctx.single_step = false;
        self.send_request(GdbStubRequest::Resume);
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
        self.send_request(GdbStubRequest::SingleStep);
        Ok(())
    }
}

impl Breakpoints for GdbStub {
    #[inline(always)]
    fn support_sw_breakpoint(&mut self) -> Option<SwBreakpointOps<'_, Self>> {
        Some(self)
    }

    #[inline(always)]
    fn support_hw_breakpoint(&mut self) -> Option<HwBreakpointOps<'_, Self>> {
        Some(self)
    }
}

impl MonitorCmd for GdbStub {
    #[inline(always)]
    fn handle_monitor_cmd(&mut self, cmd: &[u8], mut out: ConsoleOutput<'_>) -> Result<(), String> {
        let s = match std::str::from_utf8(cmd) {
            Ok(s) => s.to_string(),
            Err(err) => {
                gdbstub::outputln!(&mut out, "Expected UTF8 command input. Error was: {err}");
                return Ok(());
            }
        };
        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::MonitorCommand(s, sender));
        let response: String = recv.recv().unwrap();
        if !response.is_empty() {
            gdbstub::outputln!(&mut out, "{}", response.trim_end());
        }

        Ok(())
    }
}

impl SwBreakpoint for GdbStub {
    #[inline(always)]
    fn add_sw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        log::trace!(
            "Adding software breakpoint (kind = {:?}) to 0x{:x}",
            _kind,
            addr
        );
        if addr.rem_euclid(4) != 0 {
            return Err(TargetError::Errno(nix::errno::Errno::EINVAL as u8));
        }

        self.send_request(GdbStubRequest::AddBreakpoint(addr));

        Ok(true)
    }

    #[inline(always)]
    fn remove_sw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        log::trace!(
            "Removing software breakpoint (kind = {:?}) to 0x{:x}",
            _kind,
            addr
        );
        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::DelBreakpoint(addr, sender));
        Ok(recv.recv().unwrap())
    }
}

impl HwBreakpoint for GdbStub {
    #[inline(always)]
    fn add_hw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        log::trace!(
            "Adding hardware breakpoint (kind = {:?}) to 0x{:x}",
            _kind,
            addr
        );
        if addr.rem_euclid(4) != 0 {
            return Err(TargetError::Errno(nix::errno::Errno::EINVAL as u8));
        }
        self.send_request(GdbStubRequest::AddBreakpoint(addr));

        Ok(true)
    }

    #[inline(always)]
    fn remove_hw_breakpoint(
        &mut self,
        addr: <Self::Arch as Arch>::Usize,
        _kind: <Self::Arch as Arch>::BreakpointKind,
    ) -> TargetResult<bool, Self> {
        log::trace!(
            "Removing hardware breakpoint (kind = {:?}) to 0x{:x}",
            _kind,
            addr
        );
        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::DelBreakpoint(addr, sender));
        Ok(recv.recv().unwrap())
    }
}

impl MemoryMapXML for GdbStub {
    fn memory_map_xml(
        &self,
        offset: u64,
        length: usize,
        buf: &mut [u8],
    ) -> TargetResult<usize, Self> {
        let (sender, recv) = sync_channel(1);
        self.send_request(GdbStubRequest::MemoryMaps(sender));
        let mut memory_entries = String::new();
        for e in recv.recv().unwrap() {
            use std::fmt::Write;

            writeln!(
                &mut memory_entries,
                "<memory type=\"{type}\" start=\"0x{start:x}\" length=\"0x{length:x}\"/>#",
                r#type = if e.read_only { "rom" } else { "ram" },
                start = e.start,
                length = e.length,
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
        loop {
            if conn.peek().map(|b| b.is_some()).unwrap_or(false) {
                let byte = conn
                    .read()
                    .map_err(run_blocking::WaitForStopReasonError::Connection)?;
                return Ok(run_blocking::Event::IncomingData(byte));
            }
            if let Ok(stop_reason) = target.stop_receiver.try_recv() {
                return Ok(run_blocking::Event::TargetStopped(stop_reason));
            }
        }
    }

    fn on_interrupt(
        target: &mut Self::Target,
    ) -> Result<Option<Self::StopReason>, <Self::Target as Target>::Error> {
        target.send_request(GdbStubRequest::Interrupt);
        Ok(Some(SingleThreadStopReason::Signal(Signal::SIGINT)))
    }
}

struct SocketListener(UnixListener, std::path::PathBuf);

impl Drop for SocketListener {
    fn drop(&mut self) {
        _ = std::fs::remove_file(&self.1);
    }
}

pub fn main_loop(mut gdbstub: GdbStub, path: &std::path::Path) {
    let listener = match UnixListener::bind(path) {
        Ok(s) => SocketListener(s, path.to_path_buf()),
        Err(e) => {
            error!("Failed to create a Unix domain socket listener: {}", e);
            return;
        }
    };
    info!("Waiting for a GDB connection on {}...", path.display());

    let (stream, addr) = match listener.0.accept() {
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
}
