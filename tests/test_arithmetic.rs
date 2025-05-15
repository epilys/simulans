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

use simulans::{machine, main_loop, memory::*};

#[macro_use]
mod utils;

#[test]
fn test_sdiv() {
    _ = env_logger::builder().is_test(true).try_init();
    // Capstone output:
    // 0x40080000: sub sp, sp, #0x10
    // 0x40080004: str w0, [sp, #8]
    // 0x40080008: ldr w8, [sp, #8]
    // 0x4008000c: mov w9, #2
    // 0x40080010: sdiv w8, w8, w9
    const SDIV: &[u8] =
        b"\xff\x43\x00\xd1\xe0\x0b\x00\xb9\xe8\x0b\x40\xb9\x49\x00\x80\x52\x08\x0d\xc9\x1a";
    _ = simulans::disas(SDIV, 0);

    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new((4 * SDIV.len()) as u64).unwrap());
    let entry_point = Address(0);
    let memory = MemoryMap::builder(MEMORY_SIZE)
        .with_region(MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap())
        .unwrap()
        .build();
    let mut machine = machine::Armv8AMachine::new(memory);

    machine.cpu_state.registers.x0 = 11;
    machine.cpu_state.registers.sp = 4 * SDIV.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    main_loop(&mut machine, entry_point, SDIV).unwrap();
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

    // ```asm
    // // load a 64-bit immediate using MOV
    // .macro movq Xn, imm
    //   movz    \Xn,  \imm & 0xFFFF
    //   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
    //   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
    //   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
    // .endm
    //
    // // load a 32-bit immediate using MOV
    // .macro movl Wn, imm
    //   movz    \Wn,  \imm & 0xFFFF
    //   movk    \Wn, (\imm >> 16) & 0xFFFF, lsl 16
    // .endm
    //
    //
    // movq x0, 0xF0CACC1A
    // movl x1, 0xBEEF
    // ```

    const TEST_INPUT: &[u8] = b"\x40\x83\x99\xd2\x40\x19\xbe\xf2\x00\x00\xc0\xf2\x00\x00\xe0\xf2\xe1\xdd\x97\xd2\x01\x00\xa0\xf2";
    // _ = simulans::disas(TEST_INPUT, 0);
    // Capstone output:
    // 0x0: mov x0, #0xcc1a
    // 0x4: movk x0, #0xf0ca, lsl #16
    // 0x8: movk x0, #0, lsl #32
    // 0xc: movk x0, #0, lsl #48
    // 0x10: mov x1, #0xbeef
    // 0x14: movk x1, #0, lsl #16
    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let memory = MemoryMap::builder(MEMORY_SIZE)
        .with_region(MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap())
        .unwrap()
        .build();
    let mut machine = machine::Armv8AMachine::new(memory);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.x1, 0xbeef);
    assert_hex_eq!(machine.cpu_state.registers.x0, 0xf0cacc1a);
}
