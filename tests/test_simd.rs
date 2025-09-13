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

use simulans::{
    main_loop,
    memory::{Address, MemorySize},
};

#[macro_use]
mod utils;

#[test_log::test]
fn test_simd_rev() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_simd_rev.bin");
    // _ = simulans::disas(TEST_INPUT, 0x40080000);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x0, 0xdeadbeef);
    assert_hex_eq!(machine.cpu_state.registers.x1, 0xdeadbeefdeadbeef);
    assert_hex_eq!(machine.cpu_state.registers.x2, 0xefbeadde);
    assert_hex_eq!(machine.cpu_state.registers.x3, 0xefbeaddeefbeadde);
}

#[test_log::test]
fn test_simd_mov() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_simd_mov.bin");
    // _ = simulans::disas(TEST_INPUT, 0x40080000);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(128 machine.cpu_state.vector_registers[0], 0x80808080_80808080u64);
    assert_hex_eq!(128 machine.cpu_state.vector_registers[1], 0x0001000100010001_u64);
    assert_hex_eq!(128 machine.cpu_state.vector_registers[2], 0x0100010001000100_u64);
    assert_hex_eq!(128 machine.cpu_state.vector_registers[3], 0x01000100010001000100010001000100_u128);
    assert_hex_eq!(128 machine.cpu_state.vector_registers[4], 0x0100000001000000_u128);
    assert_hex_eq!(128 machine.cpu_state.vector_registers[5], 0x0001ffff0001ffff_u128);
}
