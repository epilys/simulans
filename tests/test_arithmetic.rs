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

#[macro_use]
mod utils;

#[test_log::test]
fn test_div() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_div.bin");
    utils::disas(TEST_INPUT, 0);

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    machine.cpu_state.registers.x0 = 11;
    machine.cpu_state.registers.sp = 4 * TEST_INPUT.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    let stack_post = machine.cpu_state.registers.sp;
    assert_eq!(stack_post, stack_pre - 0x10);
    assert_hex_eq!(machine.cpu_state.registers.x8, 0x5);
    assert_hex_eq!(machine.cpu_state.registers.x9, 0x2);
    assert_hex_eq!(machine.cpu_state.registers.x10, 0);
    assert_hex_eq!(machine.cpu_state.registers.x11, (-0x5_i32) as u32 as u64);
    assert_hex_eq!(machine.cpu_state.registers.x12, (-0x1_i32) as u32 as u64);
    assert_hex_eq!(machine.cpu_state.registers.x13, 22);
    assert_hex_eq!(machine.cpu_state.registers.x14, 0x2);
    let mem = machine.memory.find_region(entry_point).unwrap();
    let phys_offset = mem.phys_offset.0 as usize;
    let mem = mem.as_mmap().unwrap();
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset + 0x18 - 0x10],
        11
    );
}

#[test_log::test]
fn test_mov() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_mov.bin");

    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x1, 0xbeef);
    assert_hex_eq!(machine.cpu_state.registers.x0, 0xf0cacc1a);
    assert_hex_eq!(machine.cpu_state.registers.x2, 0x80803519);
    assert_hex_eq!(machine.cpu_state.registers.x23, 0xfffffffdfddfe000);
}

#[test_log::test]
fn test_bitfields() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_bitfields.bin");

    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x3, (0x55555555 & 0b111) << 5);
    assert_hex_eq!(machine.cpu_state.registers.x4, 0x55555555 & 0b11111);
    assert_hex_eq!(machine.cpu_state.registers.x5, (0x55555555 & 0b1) << 63);
}

#[test_log::test]
fn test_bitfields_2() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_bitfields_2.bin");

    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x2, 0x720);
    assert_hex_eq!(machine.cpu_state.registers.x0, 0x1cab);
    assert_hex_eq!(machine.cpu_state.registers.x3, 0xab80);
}

#[test_log::test]
fn test_bitfields_signed() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_bitfields_signed.bin");

    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x0, 0x1c85);
    // sbfx x1, x0, 2, 6
    assert_hex_eq!(
        machine.cpu_state.registers.x1,
        0b1111111111111111111111111111111111111111111111111111111111100001
    );
    // ubfx x2, x0, 2, 6
    assert_hex_eq!(
        machine.cpu_state.registers.x2,
        0b0000000000000000000000000000000000000000000000000000000000100001
    );
    // sbfx x3, x0, 2, 5
    assert_hex_eq!(machine.cpu_state.registers.x3, 1);
    // ubfx x4, x0, 2, 5
    assert_hex_eq!(
        machine.cpu_state.registers.x4,
        machine.cpu_state.registers.x3,
    );
}

#[test_log::test]
fn test_mul() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_mul.bin");
    utils::disas(TEST_INPUT, 0);

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    let x0 = machine.cpu_state.registers.x0;
    let x1 = machine.cpu_state.registers.x1;
    let x2 = machine.cpu_state.registers.x2;
    assert_hex_eq!(
        machine.cpu_state.registers.x3,
        ((x2 as u32) - (x0 as u32 * x1 as u32)) as u64
    );
    assert_hex_eq!(machine.cpu_state.registers.x4, x2 - (x0 * x1));
    assert_hex_eq!(machine.cpu_state.registers.x5, (-((x0 * x1) as i64)) as u64);
    assert_hex_eq!(
        machine.cpu_state.registers.x5,
        machine.cpu_state.registers.x6
    );
    assert_hex_eq!(
        machine.cpu_state.registers.x7,
        ((x0 as u128 * x2 as u128) >> 64) as u64
    );
}

#[test_log::test]
fn test_bit_counts() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_bit_counts.bin");
    utils::disas(TEST_INPUT, 0);

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    assert_hex_eq!(machine.cpu_state.registers.x2, 64);
    assert_hex_eq!(machine.cpu_state.registers.x3, 48);

    assert_hex_eq!(machine.cpu_state.registers.x4, 32);
    assert_hex_eq!(machine.cpu_state.registers.x5, 16);
}
