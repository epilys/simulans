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

//! Processor state types

use bilge::prelude::*;

use super::ExecutionState;

#[bitsize(2)]
#[derive(Copy, Clone, Default, FromBits, Debug, Eq, PartialEq)]
/// Exception level
pub enum ExceptionLevel {
    /// `EL0`
    EL0 = 0b00,
    #[default]
    /// `EL1`
    EL1 = 0b01,
    /// `EL2`
    EL2 = 0b10,
    /// `EL3`
    EL3 = 0b11,
}

#[bitsize(1)]
#[derive(Copy, Clone, Default, FromBits, Debug)]
/// Architectural mode, part of [`PSTATE`].
///
/// We only support `Aarch64` mode, but add an enum for it for completeness.
pub enum ArchMode {
    #[default]
    /// 64-bit mode.
    _64 = 0,
    /// 32-bit mode.
    _32 = 1,
}

#[bitsize(1)]
#[derive(Copy, Clone, Default, FromBits, Debug)]
/// Stack register selector, part of [`PSTATE`].
pub enum SpSel {
    #[default]
    /// Use `EL0` stack pointer.
    SpEl0 = 0,
    /// Use current EL's stack pointer.
    Current = 1,
}

#[bitsize(4)]
#[derive(Copy, Clone, FromBits, Default, Debug)]
/// Processing Element (PE) mode.
pub enum Mode {
    EL0 = 0b0000,
    EL1t = 0b0100,
    #[default]
    EL1h = 0b0101,
    EL1tNV = 0b1000,
    EL1hNV = 0b1001,
    #[fallback]
    Undefined = 0b1011,
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, PartialEq, Eq, FromBits, DebugBits)]
/// Condition flags pseudo-register
pub struct NZCV {
    /// Padding bits
    pub _padding2: u28,
    /// Register fields
    pub fields: NZCVFields,
    /// Padding bits
    pub _padding: u32,
}

#[bitsize(4)]
#[derive(Default, Copy, Clone, PartialEq, Eq, FromBits, DebugBits)]
pub struct NZCVFields {
    /// Overflow condition flag. (bit `[28]`)
    pub V: bool,
    /// Carry condition flag. (bit `[29]`)
    pub C: bool,
    /// Zero condition flag. (bit `[30]`)
    pub Z: bool,
    /// Negative condition flag. (bit `[31]`)
    pub N: bool,
}

#[bitsize(4)]
#[derive(Default, Copy, Clone, PartialEq, Eq, FromBits, DebugBits)]
/// `DAIF` mask bits.
pub struct DAIFFields {
    /// FIQ mask.
    pub F: bool,
    /// IRQ mask.
    pub I: bool,
    /// `SError` exception mask.
    pub A: bool,
    /// Debug mask.
    pub D: bool,
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, FromBits, DebugBits)]
/// Saved status register (`SPSR_ELx`).
pub struct SavedProgramStatusRegister {
    pub M: Mode,
    pub nRW: ArchMode,
    pub DAIF: DAIFFields,
    pub _btype: u2,
    pub _ssbs: u1,
    pub _allint: u1,
    pub __res: u6,
    pub IL: bool,
    pub SS: bool,
    pub _pan: u1,
    pub _uao: u1,
    pub _dit: u1,
    pub _tco: u1,
    pub __res0: u2,
    pub NZCV: NZCVFields,
    pub _pm: u1,
    pub _ppend: u1,
    pub _exlock: u1,
    pub _pacm: u1,
    pub _uinj: u1,
    pub _padding: u28,
}

impl SavedProgramStatusRegister {
    /// Returns what stack pointer to choose depending on [`Self::M`].
    pub fn SP(&self) -> SpSel {
        if self.M() as u32 & 0b1 == 0 {
            SpSel::SpEl0
        } else {
            SpSel::Current
        }
    }
}

#[bitsize(64)]
#[derive(Clone, Default, FromBits, DebugBits)]
#[allow(non_snake_case)]
/// `PSTATE` isn't an architectural register for `ARMv8-A`. Its bit fields are
/// accessed through special-purpose registers.
///
/// The special registers are:
///
/// | Special purpose register | Description                                                                                     | `PSTATE` fields |
/// | ------------------------ | ----------------------------------------------------------------------------------------------- | --------------- |
/// | `CurrentEL`              | Holds the current Exception level.                                                              | `EL`            |
/// | `DAIF`                   | Specifies the current interrupt mask bits.                                                      | `D, A, I, F`    |
/// | `DAIFSet`                | Sets any of the `PSTATE.{D,A, I, F}` bits to `1`                                                | `D, A, I, F`    |
/// | `DAIFClr`                | Sets any of the `PSTATE.{D,A, I, F}` bits to `0`                                                | `D, A, I, F`    |
/// | `NZCV`                   | Holds the condition flags.                                                                      | `N, Z, C, V`    |
/// | `SPSel`                  | At `EL1` or higher, this selects between the `SP` for the current Exception level and `SP_EL0`. | `SP`            |
pub struct PSTATE {
    /// Accessed through `SpSel` register.
    pub SP: SpSel,
    /// Reserved bit.
    pub _res0: u1,
    /// Current exception level.
    pub EL: ExceptionLevel,
    /// Current architectural mode.
    pub nRW: ArchMode,
    /// Interrupt mask bits.
    pub DAIF: DAIFFields,
    /// Reserved bits.
    pub _res1: u10,
    /// Illegal execution bit.
    pub IL: bool,
    /// Single-step bit.
    pub SS: bool,
    /// Reserved bits.
    pub _res2: u7,
    /// Condition flag bits.
    pub NZCV: NZCVFields,
    /// Reserved bits.
    pub _res3: u32,
}

/// Helper struct to return a referenced [`PSTATE`] view of current processor
/// state.
pub struct PSTATERef<'a> {
    #[allow(dead_code)]
    value: &'a u64,
    view: PSTATE,
}

impl std::ops::Deref for PSTATERef<'_> {
    type Target = PSTATE;

    #[inline]
    fn deref(&self) -> &PSTATE {
        &self.view
    }
}

/// Helper struct to return a mutably referenced [`PSTATE`] view of current
/// processor state.
///
/// The value is updated when the view is dropped.
pub struct PSTATERefMut<'a> {
    value: &'a mut u64,
    view: PSTATE,
}

impl std::ops::Deref for PSTATERefMut<'_> {
    type Target = PSTATE;

    #[inline]
    fn deref(&self) -> &PSTATE {
        &self.view
    }
}

impl std::ops::DerefMut for PSTATERefMut<'_> {
    #[inline]
    fn deref_mut(&mut self) -> &mut PSTATE {
        &mut self.view
    }
}

impl Drop for PSTATERefMut<'_> {
    fn drop(&mut self) {
        *self.value = self.view.clone().into();
    }
}

impl ExecutionState {
    /// Returns a view into processor state.
    pub fn PSTATE(&'_ self) -> PSTATERef<'_> {
        let view = self.registers.pstate.into();
        PSTATERef {
            value: &self.registers.pstate,
            view,
        }
    }

    /// Returns a view into processor state that updates the raw 64-bit value
    /// when dropped.
    pub fn PSTATE_mut(&'_ mut self) -> PSTATERefMut<'_> {
        let view = self.registers.pstate.into();
        PSTATERefMut {
            value: &mut self.registers.pstate,
            view,
        }
    }

    /// Generates `SPSR` value from current processor state.
    pub fn psr_from_PSTATE(&self) -> SavedProgramStatusRegister {
        let mut spsr = SavedProgramStatusRegister::from(0);
        let pstate = self.PSTATE();
        spsr.set_NZCV(pstate.NZCV());
        spsr.set_DAIF(pstate.DAIF());
        spsr.set_SS(pstate.SS());
        spsr.set_IL(pstate.IL());
        spsr.set_nRW(ArchMode::_64);
        spsr.set_M(Mode::EL1h);
        spsr
    }

    /// Returns `SPSR` value depending on current exception level.
    pub fn spsr_elx(&self) -> SavedProgramStatusRegister {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.registers.spsr_el1.into(),
            ExceptionLevel::EL2 => self.registers.spsr_el2.into(),
            ExceptionLevel::EL3 => self.registers.spsr_el3.into(),
        }
    }

    /// Sets `SPSR` value depending on current exception level.
    pub fn set_spsr_elx(&mut self, val: SavedProgramStatusRegister) {
        match self.PSTATE().EL() {
            ExceptionLevel::EL0 | ExceptionLevel::EL1 => self.registers.spsr_el1 = val.into(),
            ExceptionLevel::EL2 => self.registers.spsr_el2 = val.into(),
            ExceptionLevel::EL3 => self.registers.spsr_el3 = val.into(),
        }
    }
}
