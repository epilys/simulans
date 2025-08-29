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

use simulans::{
    devices::Device,
    disas, machine, main_loop,
    memory::{Address, MemoryMap, MemoryRegion, MemorySize},
};

mod cli;
use cli::Args;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse()?;
    let log_level = match args.verbose {
        0 => log::LevelFilter::Error,
        1 => log::LevelFilter::Info,
        2 => log::LevelFilter::Debug,
        _ => log::LevelFilter::Trace,
    };
    env_logger::Builder::new().filter_level(log_level).init();
    run_app(args)?;
    Ok(())
}

fn run_app(args: Args) -> Result<(), Box<dyn std::error::Error>> {
    let input = std::fs::read(&args.binary)?;
    // Create the machine instance, which holds the VM state.

    let dram_size = args.dram_size();
    let dram = MemoryRegion::new("ram", dram_size, args.dram_start_address())?;
    let mut memory_map_builder = MemoryMap::builder(args.memory()).with_region(dram)?;
    let pl011 = simulans::devices::pl011::PL011State::new(0);
    memory_map_builder.add_region(MemoryRegion::new_io(
        MemorySize::new(0x100).unwrap(),
        Address(0x9000000),
        pl011.ops(),
    )?)?;
    if args.generate_fdt {
        // Add Boot ROM
        let mut boot_rom = MemoryRegion::new(
            "boot-rom",
            MemorySize::new(64 * MemorySize::MiB.get()).unwrap(),
            Address(0x0),
        )?;
        if let Some(rom) = boot_rom.as_mmap_mut() {
            // Read by gdbstub's memory map XML method.
            rom.read_only = true;
        }

        memory_map_builder.add_region(boot_rom)?;
    }
    let memory = memory_map_builder.build();
    let mut machine = machine::Armv8AMachine::new(memory);
    disas(&input, args.entry_point_address().0)?;
    if args.generate_fdt {
        let fdt = machine.generate_fdt(args.entry_point_address())?;
        if let Some(ref dump_dtb) = args.dump_dtb {
            std::fs::write(dump_dtb, &fdt.bytes).map_err(|err| {
                format!(
                    "Could not write fdt blob of {} bytes to {}: {err}",
                    fdt.bytes.len(),
                    dump_dtb.display()
                )
            })?;
        }
    }

    if let Some(path) = args.gdb_stub_path.as_ref() {
        machine.load_code(&input, args.entry_point_address())?;
        let gdb_stub = simulans::gdb::GdbStub::new(machine, args.entry_point_address());
        simulans::gdb::main_loop(gdb_stub, path);
    } else {
        main_loop(&mut machine, args.entry_point_address(), &input)?;
    }

    Ok(())
}
