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
    disas(&input)?;
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
