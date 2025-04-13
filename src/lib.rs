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

#![doc = include_str!("../README.md")]
//!
//! # Cross-references in source code
//!
//! We use [**`tagref`**](https://github.com/stepchowfun/tagref) annotations to manage
//! cross-references inside source-code. You do not have to use the CLI itself,
//! it's useful to verify that references are valid and also list/query
//! references. Otherwise you can just search for tag/ref names manually when
//! browsing source code.
//!
//! Their main use is tracking places of code that lack implementation of
//! specific features (such as memory atomics).
//!
//! ## Authoritative tags
//!
//! Tags need to be declared exactly once in source code. Here follows a list,
//! which since it's included in the source as `rustdoc` comments, they are also
//! tag definitions.
//!
//! ### Generic Code/implementation tags
//!
//! - `[tag:TODO]: General TODO items.`
//! - `[tag:FIXME]: General FIXME items.`
//! - `[tag:dubious_implementation]: Code that is most definitely not
//!   implemented correctly.`
//! - `[tag:verify_implementation]: Code that we should look back at with fresh
//!   eyes.`
//!
//! ### Architectural feature tags
//!
//! - `[tag:memory_ordering]: Code that implements memory ordering.`
//! - `[tag:atomics]: Code that implements exclusive memory access.`
//! - `[tag:can_trap]: Code that can trap.`
//!
//! ### Peripheral (device model) tags
//!
//! - `[tag:interrupts]: Gicv2/Gicv3 related.`
//! - `[tag:serial]: serial output.`
pub mod cpu_state;
pub mod jit;
pub mod machine;
pub mod memory;

/// Disassembles and prints each decoded aarch64 instruction to stdout using
/// Capstone library, for debugging.
pub fn disas(input: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    use capstone::prelude::*;

    let mut cs = Capstone::new()
        .arm64()
        .mode(capstone::arch::arm64::ArchMode::Arm)
        .endian(capstone::Endian::Little)
        .detail(true)
        .build()
        .expect("Failed to create Capstone object");
    cs.set_syntax(capstone::Syntax::Intel)?;
    let decoded_iter = cs.disasm_all(input, 0x40080000)?;
    eprintln!("Capstone output:");
    for insn in decoded_iter.as_ref() {
        eprintln!("{}", insn);
    }
    Ok(())
}

pub fn main_loop(
    machine: &mut machine::Armv8AMachine,
    start_address: usize,
    code: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    let mut jit_block = jit::JitContext::new();
    machine.load_code(code, start_address)?;
    machine.pc = start_address.try_into().unwrap();
    let mut func = machine.lookup_entry_func;
    while machine.halted == 0 {
        func = (func.0)(&mut jit_block, machine);
        if machine.prev_pc == machine.pc {
            break;
        }
    }
    Ok(())
}
