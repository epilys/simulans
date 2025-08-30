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

#[test]
fn test_sdiv() {
    _ = env_logger::builder().is_test(true).try_init();
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_sdiv.bin");
    _ = simulans::disas(TEST_INPUT, 0);
    // Capstone output:
    // 0x40080000: sub sp, sp, #0x10
    // 0x40080004: str w0, [sp, #8]
    // 0x40080008: ldr w8, [sp, #8]
    // 0x4008000c: mov w9, #2
    // 0x40080010: sdiv w8, w8, w9

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
    assert_eq!(machine.cpu_state.registers.x8, 5);
    assert_eq!(machine.cpu_state.registers.x9, 2);
    let mem = machine.memory.find_region(entry_point).unwrap();
    let phys_offset = mem.phys_offset.0 as usize;
    let mem = mem.as_mmap().unwrap();
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset + 0x18 - 0x10],
        11
    );
}

#[test]
fn test_mov() {
    _ = env_logger::builder().is_test(true).try_init();

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_mov.bin");

    // _ = simulans::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x1, 0xbeef);
    assert_hex_eq!(machine.cpu_state.registers.x0, 0xf0cacc1a);
    assert_hex_eq!(machine.cpu_state.registers.x2, 0x80803519);
}

#[test]
fn test_bitfields() {
    _ = env_logger::builder().is_test(true).try_init();

    // ```asm
    // // load a 64-bit immediate using MOV
    // .macro movq Xn, imm
    //   movz    \Xn,  \imm & 0xFFFF
    //   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
    //   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
    //   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
    // .endm
    //
    // movq x1, 0x55555555
    // ubfiz   x3, x1, 5, 3
    // ubfiz   x4, x1, 0, 5
    // ubfiz   x5, x1, 63, 1
    // ```

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_bitfields.bin");

    _ = simulans::disas(TEST_INPUT, 0);
    // Capstone output:
    // 0x0: mov x1, #0x5555
    // 0x4: movk x1, #0x5555, lsl #16
    // 0x8: movk x1, #0, lsl #32
    // 0xc: movk x1, #0, lsl #48
    // 0x10: mov x2, #0xaaaa
    // 0x14: movk x2, #0xaaaa, lsl #16
    // 0x18: movk x2, #0, lsl #32
    // 0x1c: movk x2, #0, lsl #48
    // 0x20: ubfiz x3, x1, #5, #3
    // 0x24: ubfx x4, x1, #0, #5
    // 0x28: lsl x5, x1, #0x3f
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x3, (0x55555555 & 0b111) << 5);
    assert_hex_eq!(machine.cpu_state.registers.x4, 0x55555555 & 0b11111);
    assert_hex_eq!(machine.cpu_state.registers.x5, (0x55555555 & 0b1) << 63);
}

#[test]
fn test_bitfields_2() {
    _ = env_logger::builder().is_test(true).try_init();

    // ```asm
    // // load a 64-bit immediate using MOV
    // .macro movq Xn, imm
    //   movz    \Xn,  \imm & 0xFFFF
    //   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
    //   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
    //   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
    // .endm
    //
    // movq x0, 0x1c80
    // ubfx	w2, w0, #2, #14
    // ```

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_bitfields_2.bin");

    // _ = simulans::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x2, 0x720);
}
