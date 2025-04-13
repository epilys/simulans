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

use simulans::{disas, machine, main_loop};

mod cli;
use cli::Args;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = Args::parse()?;
    match args.verbose {
        0 => log::set_max_level(log::LevelFilter::Off),
        1 => log::set_max_level(log::LevelFilter::Info),
        2 => log::set_max_level(log::LevelFilter::Debug),
        _ => log::set_max_level(log::LevelFilter::Trace),
    }
    run_app(args)?;
    Ok(())
}

fn run_app(args: Args) -> Result<(), Box<dyn std::error::Error>> {
    let input = std::fs::read(&args.binary)?;
    // Create the machine instance, which holds the VM state.
    let mut machine = machine::Armv8AMachine::new(args.memory);
    disas(&input, args.start_address.0)?;
    if args.generate_fdt {
        machine.generate_fdt(args.start_address)?;
    }

    main_loop(
        &mut machine,
        args.start_address.0.try_into().unwrap(),
        &input,
    )?;
    // let sp_el0 = run_aarch64(&mut machine, &input, args.start_address.0)?;
    // log::trace!("sp_el0 = 0x{:x}", sp_el0);
    // log::trace!("cpu state after running is {:#?}", &machine.cpu_state);
    Ok(())
}

// fn run_aarch64(
//     machine: &mut machine::Armv8AMachine,
//     input: &[u8],
//     start_address: u64,
// ) -> Result<i64, Box<dyn std::error::Error>> {
//     let ret: i64 = unsafe { run_code(machine, start_address.try_into()?,
// input, ())? };     Ok(ret)
// }
