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

use simulans::{disas, jit, run_code};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();
    let args = std::env::args_os().collect::<Vec<_>>();
    let input = match args.len() {
        2 => std::fs::read(&args[1])?,
        other => {
            eprintln!("Error: one argument is expected, but got {other}");
            std::process::exit(1);
        }
    };
    // Create the JIT instance, which manages all generated functions and data.
    let mut jit = jit::Armv8AMachine::default();

    disas(&input)?;
    let sp_el0 = run_aarch64(&mut jit, &input)?;
    log::trace!("sp_el0 = 0x{:x}", sp_el0);
    log::trace!("cpu state after running is {:#?}", &jit.cpu_state);
    Ok(())
}

fn run_aarch64(
    jit: &mut jit::Armv8AMachine,
    input: &[u8],
) -> Result<i64, Box<dyn std::error::Error>> {
    let ret: i64 = unsafe { run_code(jit, input, ())? };
    Ok(ret)
}
