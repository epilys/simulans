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
//! - `[tag:needs_unit_test]: Needs a corresponding unit test.`
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
//! - `[tag:FEAT_CSSC]: Common Short Sequence Compression.` Neither Capstone nor
//!   Binja seem to be able to decode this feature's instructions.
//! - `[tag:have_sve]:` <https://developer.arm.com/documentation/ddi0596/2020-12/Shared-Pseudocode/AArch64-Functions?lang=en#aarch64.functions.sve.HaveSVE>.
//!
//! ### Peripheral (device model) tags
//!
//! - `[tag:interrupts]: Gicv2/Gicv3 related.`
//! - `[tag:serial]: serial output.`

#![deny(
    unsafe_op_in_unsafe_fn,
    // rustdoc
    rustdoc::redundant_explicit_links,
    rustdoc::broken_intra_doc_links,
    // clippy
    // groups
    clippy::correctness,
    clippy::suspicious,
    clippy::complexity,
    clippy::perf,
    clippy::cargo,
    clippy::nursery,
    clippy::style,
    clippy::lint_groups_priority,
    // restriction
    clippy::as_underscore,
    clippy::assertions_on_result_states,
    clippy::dbg_macro,
    clippy::missing_safety_doc,
    clippy::rc_buffer,
    clippy::undocumented_unsafe_blocks,
    // pedantic
    clippy::bool_to_int_with_if,
    clippy::borrow_as_ptr,
    clippy::case_sensitive_file_extension_comparisons,
    clippy::cast_lossless,
    // This lint is only useful for non-64bit targets which we do not... target.
    // clippy::cast_possible_wrap,
    clippy::cast_ptr_alignment,
    clippy::doc_markdown,
    clippy::expect_fun_call,
    clippy::into_iter_without_iter,
    clippy::large_futures,
    clippy::manual_hash_one,
    clippy::or_fun_call,
    clippy::ptr_as_ptr,
    clippy::struct_field_names,
    clippy::unnecessary_fallible_conversions,
    clippy::unused_enumerate_index,
    clippy::waker_clone_wake,
)]
#![allow(clippy::multiple_crate_versions, clippy::cognitive_complexity)]

#[cfg(not(target_pointer_width = "64"))]
core::compile_error!("Can only be compiled on targets with 64bit address support");

pub mod cpu_state;
pub mod devices;
pub mod fdt;
pub mod gdb;
pub mod interval_tree;
pub mod jit;
pub mod machine;
pub mod memory;

/// Disassembles and prints each decoded aarch64 instruction to stdout using
/// Capstone library, for debugging.
pub fn disas(input: &[u8], starting_address: u64) -> Result<(), Box<dyn std::error::Error>> {
    use capstone::prelude::*;

    let mut cs = Capstone::new()
        .arm64()
        .mode(capstone::arch::arm64::ArchMode::Arm)
        .endian(capstone::Endian::Little)
        .detail(true)
        .build()
        .expect("Failed to create Capstone object");
    cs.set_syntax(capstone::Syntax::Intel)?;
    let decoded_iter = cs.disasm_all(input, starting_address)?;
    log::trace!("Capstone output:");
    for insn in decoded_iter.as_ref() {
        log::trace!("{}", insn);
    }
    Ok(())
}

pub fn main_loop(
    machine: &mut machine::Armv8AMachine,
    start_address: memory::Address,
    code: &[u8],
) -> Result<(), Box<dyn std::error::Error>> {
    let mut jit_ctx = jit::JitContext::new();
    jit_ctx.single_step = false;
    machine.load_code(code, start_address)?;
    if machine.pc == 0 {
        machine.pc = start_address.0;
    }
    let mut func = machine.lookup_entry_func;
    while machine.halted == 0 {
        func = (func.0)(&mut jit_ctx, machine);
    }
    Ok(())
}
