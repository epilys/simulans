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

use crate::{
    cpu_state::{ArchMode, DAIFFields, Exception, ExceptionLevel, SpSel},
    memory::Address,
};

macro_rules! bitmask {
    ( $off: expr, $len: expr ) => {
        ((1 << $len) - 1) << $off
    };
}

macro_rules! getbits {
    ( $val: expr, $off: expr, $len: expr ) => {
        ($val & bitmask!($off, $len)) >> $off
    };
}

macro_rules! setbits {
    ( $var: expr, $off: expr, $len: expr, $val: expr ) => {
        ($var & !bitmask!($off, $len)) | (($val << $off) & bitmask!($off, $len))
    };
}

#[bitsize(49)]
#[derive(Copy, Clone, Default, FromBits, DebugBits)]
pub struct IssType {
    pub iss: u25,
    pub iss2: u24,
}

pub struct FullAddress {
    pub paspace: PASpace,
    // 56 bits
    pub address: u64,
}

/// Physical address spaces
pub enum PASpace {
    UNKNOWN = 0,
    Root,
    SystemAgent,
    NonSecureProtected,
    // Reserved
    NA6,
    // Reserved
    NA7,
    Realm,
    Secure,
    NonSecure,
}

// <https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/shared-exceptions-exceptions?lang=en#shared.exceptions.exceptions.ExceptionRecord>
pub struct ExceptionRecord {
    // Exception class
    pub exceptype: Exception,
    // Syndrome record
    pub syndrome: IssType,
    // Physical fault address
    pub paddress: FullAddress,
    // Virtual fault address
    pub vaddress: u64,
    // Validity of Intermediate Physical fault address
    pub ipavalid: bool,
    // Validity of Physical fault address
    pub pavalid: bool,
    // Intermediate Physical fault address space
    pub NS: bool,
    // Intermediate Physical fault address (56 bits)
    pub ipaddress: u64,
    // Trapped SVC or SMC instruction
    pub trappedsyscallinst: bool,
}

impl ExceptionRecord {
    /// Return a blank exception syndrome record for an exception of the given
    /// type.
    ///
    /// <https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/shared-exceptions-exceptions?lang=en#shared.exceptions.exceptions.ExceptionSyndrome>
    pub fn exception_syndrome(exceptype: Exception) -> Self {
        Self {
            exceptype,
            syndrome: IssType::new(u25::new(0), u24::new(0)),
            vaddress: 0x0,
            ipavalid: false,
            pavalid: false,
            NS: false,
            ipaddress: 0x0,
            paddress: FullAddress {
                paspace: PASpace::UNKNOWN,
                address: 0x0, // bits(56) UNKNOWN,
            },
            trappedsyscallinst: false,
        }
    }
}

/// Raise an "Undefined" exception
///
/// [AArch64.Undefined](https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/aarch64-exceptions-traps?lang=en#aarch64.exceptions.traps.AArch64.Undefined)
pub extern "C" fn aarch64_undefined(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
) {
    tracing::event!(target: "exception", tracing::Level::TRACE, "AArch64.Undefined");
    let current_el = machine.cpu_state.pstate.EL();

    let route_to_el2 =
        matches!(current_el, ExceptionLevel::EL0) && machine.cpu_state.EL2_enabled() && {
            // HCR_EL2.TGE == '1';
            machine.cpu_state.registers.hcr_el2 & (1 << 27) > 0
        };
    let vect_offset = Address(0x0);
    let except = ExceptionRecord::exception_syndrome(Exception::Uncategorized);

    if current_el as u32 > ExceptionLevel::EL1 as u32 {
        aarch64_take_exception(
            machine,
            current_el,
            except,
            preferred_exception_return,
            vect_offset,
        );
    } else if route_to_el2 {
        aarch64_take_exception(
            machine,
            ExceptionLevel::EL2,
            except,
            preferred_exception_return,
            vect_offset,
        );
    } else {
        aarch64_take_exception(
            machine,
            ExceptionLevel::EL1,
            except,
            preferred_exception_return,
            vect_offset,
        );
    }
}

pub fn aarch64_take_exception(
    machine: &mut crate::machine::Armv8AMachine,
    target_el: ExceptionLevel,
    _exception: ExceptionRecord,
    preferred_exception_return: Address,
    vect_offset: Address,
) {
    if machine
        .exit_request
        .load(std::sync::atomic::Ordering::SeqCst)
        > 0
    {
        return;
    }
    assert!(machine.cpu_state.have_el(target_el));
    //assert!(!ELUsingAArch32(target_el));
    assert!(target_el as u32 >= machine.cpu_state.pstate.EL() as u32);

    let mut adjusted_vect_offset = vect_offset;

    if target_el as u32 > machine.cpu_state.pstate.EL() as u32 {
        // Skip aarch32, we don't support it.
        // let lower_32: bool = if target_el == ExceptionLevel::EL3 {
        //     if machine.cpu_state.EL2_enabled() {
        //         ELUsingAArch32(ExceptionLevel::EL2)
        //     } else {
        //         ELUsingAArch32(ExceptionLevel::EL1)
        //     }
        // } else if machine.cpu_state.is_in_host()
        //     && machine.cpu_state.pstate.EL == ExceptionLevel::EL0
        //     && target_el == ExceptionLevel::EL2
        // {
        //     ELUsingAArch32(ExceptionLevel::EL0)
        // } else {
        //     ELUsingAArch32(target_el - 1)
        // };
        let lower_32 = false;
        adjusted_vect_offset += if lower_32 { 0x600_u64 } else { 0x400 };
    } else if matches!(machine.cpu_state.pstate.SP(), SpSel::Current) {
        adjusted_vect_offset += 0x200_u64;
    }
    tracing::event!(
        target: "exception",
        tracing::Level::TRACE,
        current_el = ?machine.cpu_state.pstate.EL(),
        ?target_el,
        ?vect_offset,
        ?adjusted_vect_offset,
        ?preferred_exception_return,
        "vbar: 0x{:x?}",
        machine.cpu_state.vbar_elx()
    );

    // bits(64) spsr = GetPSRFromPSTATE(AArch64_NonDebugState, 64);
    let spsr = machine.cpu_state.psr_from_PSTATE();
    machine.cpu_state.pstate.set_EL(target_el);
    machine.cpu_state.pstate.set_nRW(ArchMode::_64);
    machine.cpu_state.pstate.set_SP(SpSel::Current);

    // SPSR_ELx[] = spsr;
    machine.cpu_state.set_spsr_elx(spsr);

    // ELR_ELx[] = preferred_exception_return;
    machine.cpu_state.set_elr_elx(preferred_exception_return.0);

    machine.cpu_state.pstate.set_SS(false);
    // PSTATE.<D,A,I,F> = '1111';
    machine
        .cpu_state
        .pstate
        .set_DAIF(DAIFFields::new(true, true, true, true));
    machine.cpu_state.pstate.set_IL(false);

    let vbar_elx = machine.cpu_state.vbar_elx();

    // VBAR_ELx[]<63:11>:vect_offset<10:0>
    machine.pc = setbits!(vbar_elx, 0, 11, getbits!(vect_offset.0, 0, 11));
}
