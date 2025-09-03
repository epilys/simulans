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

mod map;
mod region;

mod address;
mod size;

pub use address::*;
pub use map::*;
pub use region::*;
pub use size::*;

//#[repr(transparent)]
//#[derive(Clone, Copy)]
///// An "entry" function for a block.
/////
///// It can be either a JIT compiled translation block, or a special emulator
///// function.
//pub type Entry(pub extern "C" fn(&mut JitContext, &mut Armv8AMachine) ->
// Entry);

/// Default guest physical address to load kernel code to.
pub const KERNEL_ADDRESS: usize = 0x40080000;

// Default starting offset of DRAM inside the physical address space.
pub const PHYS_MEM_START: u64 = 0x4000_0000;

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd)]
#[repr(i32)]
/// Register/memory width in bits.
pub enum Width {
    _128 = 128,
    _64 = 64,
    _32 = 32,
    _16 = 16,
    _8 = 8,
}

impl From<Width> for cranelift::prelude::Type {
    fn from(width: Width) -> Self {
        use cranelift::codegen::ir::types::{I128, I16, I32, I64, I8};

        match width {
            Width::_8 => I8,
            Width::_16 => I16,
            Width::_32 => I32,
            Width::_64 => I64,
            Width::_128 => I128,
        }
    }
}
