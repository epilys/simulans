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

/// Test a simple function that squares its input.
#[test_log::test]
fn test_square() {
    // This code was compiled from this C function:
    // ```c
    //  int square(int num) {
    //    return num * num;
    //  }
    // ```
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_square.bin");
    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
    machine.cpu_state.registers.sp_el1 = 4 * TEST_INPUT.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp_el1;
    // Pass "25" as `num`
    machine.cpu_state.registers.x0 = 25;
    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x0, 625);
    assert_hex_eq!(machine.cpu_state.registers.x8, 25);
    assert_hex_eq!(machine.cpu_state.registers.x9, 25);
    let stack_post = machine.cpu_state.registers.sp_el1;
    assert_hex_eq!(stack_post, stack_pre);
}

/// Test a str and a load from the stack
#[test_log::test]
fn test_load_stores() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_load_stores.bin");
    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
    machine.cpu_state.registers.sp_el1 = 4 * TEST_INPUT.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp_el1;
    machine.cpu_state.registers.x0 = 0xbadbeef;
    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    let stack_post = machine.cpu_state.registers.sp_el1;
    assert_eq!(stack_post, stack_pre);
    let mem = machine.memory.find_region(entry_point).unwrap();
    let phys_offset = mem.phys_offset.0 as usize;
    let mem = mem.as_mmap().unwrap();
    assert_eq!(mem.as_ref()[stack_post as usize - phys_offset - 0x10], 0xef);
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset - 0x10 + 1],
        0xbe
    );
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset - 0x10 + 2],
        0xad
    );
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset - 0x10 + 3],
        0x0b
    );
    assert_hex_eq!(machine.cpu_state.registers.x0, 0xbadbeef);
    assert_hex_eq!(machine.cpu_state.registers.x1, 0xbadbeef);
}

/// Test a load stores adds and moves in the stack
#[test_log::test]
fn test_load_stores_2() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_load_stores_2.bin");
    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
    machine.cpu_state.registers.sp_el1 = 4 * TEST_INPUT.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp_el1;
    machine.cpu_state.registers.x0 = 0xbadbeef;
    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    let stack_post = machine.cpu_state.registers.sp_el1;
    assert_eq!(stack_post, stack_pre);
    assert_hex_eq!(machine.cpu_state.registers.x0, 2 * 0x1234);
    assert_hex_eq!(machine.cpu_state.registers.x1, 0x1234);
    let mem = machine.memory.find_region(entry_point).unwrap();
    let phys_offset = mem.phys_offset.0 as usize;
    let mem = mem.as_mmap().unwrap();
    assert_eq!(mem.as_ref()[stack_post as usize - phys_offset - 0x10], 0x34);
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset - 0x10 + 1],
        0x12
    );
}
