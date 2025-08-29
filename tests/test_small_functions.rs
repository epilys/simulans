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

use simulans::{devices::Device, machine, main_loop, memory::*};

#[macro_use]
mod utils;

/// Test a simple function that squares its input.
#[test]
fn test_square() {
    // This code was compiled from this C function:
    // ```c
    //  int square(int num) {
    //    return num * num;
    //  }
    // ```
    const SQUARED: &[u8] = b"\x02\x00\x00\x94\x08\x00\x00\x14\xff\x43\x00\xd1\xe0\x0f\x00\xb9\xe8\x0f\x40\xb9\xe9\x0f\x40\xb9\x00\x7d\x09\x1b\xff\x43\x00\x91\xc0\x03\x5f\xd6\x1f\x20\x03\xd5";
    // _ = simulans::disas(SQUARED, 0);
    // Capstone disassembly:
    //
    // Capstone output:
    // 0x0: bl #8
    // 0x4: b #0x24
    // 0x8: sub sp, sp, #0x10
    // 0xc: str w0, [sp, #0xc]
    // 0x10: ldr w8, [sp, #0xc]
    // 0x14: ldr w9, [sp, #0xc]
    // 0x18: mul w0, w8, w9
    // 0x1c: add sp, sp, #0x10
    // 0x20: ret
    // 0x24: nop
    // ```

    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new((4 * SQUARED.len()) as u64).unwrap());
    let entry_point = Address(0);
    let memory = MemoryMap::builder()
        .with_region(MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap())
        .unwrap()
        .build();
    let mut machine = machine::Armv8AMachine::new(memory);
    machine.cpu_state.registers.sp = 4 * SQUARED.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    // Pass "25" as `num`
    machine.cpu_state.registers.x0 = 25;
    main_loop(&mut machine, entry_point, SQUARED).unwrap();
    assert_eq!(machine.cpu_state.registers.x0, 625);
    assert_eq!(machine.cpu_state.registers.x8, 25);
    assert_eq!(machine.cpu_state.registers.x9, 25);
    let stack_post = machine.cpu_state.registers.sp;
    assert_eq!(stack_post, stack_pre);
}

/// Test a str and a load from the stack
#[test]
fn test_load_stores() {
    // Capstone output:
    // 0x40080000: str x0, [sp, #-0x10]!
    // 0x40080004: ldr x1, [sp], #0x10
    const LOAD_STORES: &[u8] = b"\xe0\x0f\x1f\xf8\xe1\x07\x41\xf8";
    // _ = simulans::disas(LOAD_STORES, 0);

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * LOAD_STORES.len()) as u64).unwrap());
    let entry_point = Address(0);
    let memory = MemoryMap::builder()
        .with_region(MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap())
        .unwrap()
        .build();
    let mut machine = machine::Armv8AMachine::new(memory);
    machine.cpu_state.registers.sp = 4 * LOAD_STORES.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    machine.cpu_state.registers.x0 = 0xbadbeef;
    main_loop(&mut machine, entry_point, LOAD_STORES).unwrap();
    let stack_post = machine.cpu_state.registers.sp;
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
    assert_eq!(machine.cpu_state.registers.x0, 0xbadbeef);
    assert_eq!(machine.cpu_state.registers.x1, 0xbadbeef);
}

/// Test a load stores adds and moves in the stack
#[test]
fn test_load_stores_2() {
    // Capstone output:
    // 0x40080000: mov x0, #0x1234
    // 0x40080004: str x0, [sp, #-0x10]!
    // 0x40080008: ldr x1, [sp], #0x10
    // 0x4008000c: add x0, x0, x1
    const STACK_ADD: &[u8] = b"\x80\x46\x82\xd2\xe0\x0f\x1f\xf8\xe1\x07\x41\xf8\x00\x00\x01\x8b";
    // _ = simulans::disas(STACK_ADD, 0);

    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new((4 * STACK_ADD.len()) as u64).unwrap());
    let entry_point = Address(0);
    let memory = MemoryMap::builder()
        .with_region(MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap())
        .unwrap()
        .build();
    let mut machine = machine::Armv8AMachine::new(memory);
    machine.cpu_state.registers.sp = 4 * STACK_ADD.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    machine.cpu_state.registers.x0 = 0xbadbeef;
    main_loop(&mut machine, entry_point, STACK_ADD).unwrap();
    let stack_post = machine.cpu_state.registers.sp;
    assert_eq!(stack_post, stack_pre);
    assert_eq!(machine.cpu_state.registers.x0, 2 * 0x1234);
    assert_eq!(machine.cpu_state.registers.x1, 0x1234);
    let mem = machine.memory.find_region(entry_point).unwrap();
    let phys_offset = mem.phys_offset.0 as usize;
    let mem = mem.as_mmap().unwrap();
    assert_eq!(mem.as_ref()[stack_post as usize - phys_offset - 0x10], 0x34);
    assert_eq!(
        mem.as_ref()[stack_post as usize - phys_offset - 0x10 + 1],
        0x12
    );
}

/// Test exception levels
#[test]
fn test_exception_levels() {
    // Capstone output:
    // 0x40080000: mov x0, #1
    // 0x40080004: orr x0, x0, #2
    // 0x40080008: orr x0, x0, #4
    // 0x4008000c: orr x0, x0, #8
    // 0x40080010: orr x0, x0, #0x100
    // 0x40080014: orr x0, x0, #0x400
    // 0x40080018: orr x0, x0, #0x800
    // 0x4008001c: msr scr_el3, x0
    // 0x40080020: orr w0, wzr, #8
    // 0x40080024: orr x0, x0, #0x10
    // 0x40080028: orr x0, x0, #0x80000000
    // 0x4008002c: msr hcr_el2, x0
    // 0x40080030: mrs x0, midr_el1
    // 0x40080034: msr vpidr_el2, x0
    // 0x40080038: mrs x0, mpidr_el1
    // 0x4008003c: msr vmpidr_el2, x0
    // 0x40080040: msr vttbr_el2, xzr
    // 0x40080044: msr sctlr_el2, xzr
    // 0x40080048: msr sctlr_el1, xzr
    // 0x4008004c: ldr x0, #0x40080068
    // 0x40080050: msr elr_el3, x0
    // 0x40080054: ldr x0, #0x40080070
    // 0x40080058: msr spsr_el3, x0
    // 0x4008005c: eret
    // 0x40080060: nop
    const BOOT: &[u8] = b"\x20\x00\x80\xd2\x00\x00\x7f\xb2\x00\x00\x7e\xb2\x00\x00\x7d\xb2\x00\x00\x78\xb2\x00\x00\x76\xb2\x00\x00\x75\xb2\x00\x11\x1e\xd5\xe0\x03\x1d\x32\x00\x00\x7c\xb2\x00\x00\x61\xb2\x00\x11\x1c\xd5\x00\x00\x38\xd5\x00\x00\x1c\xd5\xa0\x00\x38\xd5\xa0\x00\x1c\xd5\x1f\x21\x1c\xd5\x1f\x10\x1c\xd5\x1f\x10\x18\xd5\xe0\x00\x00\x58\x20\x40\x1e\xd5\xe0\x00\x00\x58\x00\x40\x1e\xd5\xe0\x03\x9f\xd6\x1f\x20\x03\xd5\x00\x00\x00\x00\xd8\x00\x40\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";
    // _ = simulans::disas(BOOT, 0);

    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new((4 * BOOT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let memory = MemoryMap::builder()
        .with_region(MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap())
        .unwrap()
        .build();
    let mut machine = machine::Armv8AMachine::new(memory);
    machine.cpu_state.registers.sp = 4 * BOOT.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    main_loop(&mut machine, entry_point, BOOT).unwrap();
    let stack_post = machine.cpu_state.registers.sp;
    assert_eq!(stack_post, stack_pre);
    assert_eq!(machine.cpu_state.registers.x0, 0);
    assert_eq!(machine.cpu_state.registers.hcr_el2, 0x80000018);
    assert_eq!(machine.cpu_state.registers.scr_el3, 0xd0f);
    assert_eq!(machine.cpu_state.registers.elr_el3, 0x4000d8);
}

#[test]
fn test_uart_write_str() {
    _ = env_logger::builder().is_test(true).try_init();

    const TEST_INPUT: &[u8] = b"\xde\x02\x00\x10\x02\x02\x00\xb4\x21\x02\x00\x10\x29\x00\x02\x8b\x2a\x14\x40\x38\x0b\x34\x40\x79\xeb\x00\x28\x37\x3f\x00\x09\xeb\x0a\x00\x00\x79\x00\x01\x00\x54\x2a\x14\x40\x38\x0b\x34\x40\x79\x6b\xff\x2f\x36\xdf\x3f\x03\xd5\x0b\x34\x40\x79\xcb\xff\x2f\x37\xf7\xff\xff\x17\xe0\x03\x1f\x2a\xc0\x03\x5f\xd6\x48\x65\x6c\x6c\x6f\x20\x77\x6f\x72\x6c\x64\x0a\x1f\x20\x03\xd5";

    const DRAM_MEMORY_SIZE: MemorySize = MemorySize(NonZero::new(TEST_INPUT.len() as u64).unwrap());

    _ = simulans::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let pl011_addr = Address(TEST_INPUT.len() as u64);
    {
        let pl011 = simulans::devices::pl011::PL011State::new(0);
        let memory = MemoryMap::builder()
            .with_region(MemoryRegion::new("ram", DRAM_MEMORY_SIZE, entry_point).unwrap())
            .unwrap()
            .with_region(
                MemoryRegion::new_io(MemorySize::new(0x100).unwrap(), pl011_addr, pl011.ops())
                    .unwrap(),
            )
            .unwrap()
            .build();
        let mut machine = machine::Armv8AMachine::new(memory);
        machine.cpu_state.registers.x0 = pl011_addr.0;
        machine.cpu_state.registers.x2 = "Hello world\n".len() as u64;

        main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        assert_hex_eq!(reg!(x0), 0x0);
    }
}
