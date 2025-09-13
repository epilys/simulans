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

use std::num::NonZero;

use simulans::{main_loop, memory::*};

mod utils;

#[test_log::test]
fn test_simple_if() {
    const FOOBAR: &[u8] = include_bytes!("./inputs/test_simple_if_opt.bin");
    _ = simulans::disas(FOOBAR, 0);
    const FOOBAR_UNOPT: &[u8] = include_bytes!("./inputs/test_simple_if.bin");
    // _ = simulans::disas(FOOBAR_UNOPT, 0);

    let entry_point = Address(0);
    {
        const MEMORY_SIZE: MemorySize =
            MemorySize(NonZero::new((4 * FOOBAR_UNOPT.len()) as u64).unwrap());
        {
            let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

            // Pass "10" as `num`
            machine.cpu_state.registers.x0 = 10;
            machine.cpu_state.registers.sp = 4 * FOOBAR_UNOPT.len() as u64 - 4;
            main_loop(&mut machine, entry_point, FOOBAR_UNOPT).unwrap();
            assert_hex_eq!(machine.cpu_state.registers.x0, 20);
        }
        {
            let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

            // Pass "11" as `num`
            machine.cpu_state.registers.x0 = 11;
            machine.cpu_state.registers.sp = 4 * FOOBAR_UNOPT.len() as u64 - 4;
            main_loop(&mut machine, entry_point, FOOBAR_UNOPT).unwrap();
            assert_hex_eq!(machine.cpu_state.registers.x0, 11 * 11,);
        }
    }
    // Optimized version
    {
        const MEMORY_SIZE: MemorySize =
            MemorySize(NonZero::new((4 * FOOBAR.len()) as u64).unwrap());
        {
            let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

            // Pass "10" as `num`
            machine.cpu_state.registers.x0 = 10;
            machine.cpu_state.registers.sp = 4 * FOOBAR.len() as u64 - 4;
            main_loop(&mut machine, entry_point, FOOBAR).unwrap();
            assert_hex_eq!(machine.cpu_state.registers.x0, 20);
        }
        {
            let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

            // Pass "11" as `num`
            machine.cpu_state.registers.x0 = 11;
            machine.cpu_state.registers.sp = 4 * FOOBAR.len() as u64 - 4;
            main_loop(&mut machine, entry_point, FOOBAR).unwrap();
            assert_hex_eq!(machine.cpu_state.registers.x0, 11 * 11,);
        }
    }
}
