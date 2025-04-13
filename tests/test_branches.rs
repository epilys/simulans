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

use simulans::{machine, main_loop, memory::MemorySize};

#[test]
fn test_simple_if() {
    // This code was compiled from this C function:
    // ```c
    /* Type your code here, or load an example. */
    //int foobar(int num) {
    //    if ((num % 2) == 0 ) {
    //        return 2 * num;
    //    }
    //    return num * num;
    //}
    // ```
    // Unoptimized (`-O0`) armv8-a clang assembly:
    // ```asm
    // foobar:
    //         sub     sp, sp, #16
    //         str     w0, [sp, #8]
    //         ldr     w8, [sp, #8]
    //         mov     w10, #2
    //         sdiv    w9, w8, w10
    //         mul     w9, w9, w10
    //         subs    w8, w8, w9
    //         cbnz    w8, .LBB0_2
    //         b       .LBB0_1
    // .LBB0_1:
    //         ldr     w9, [sp, #8]
    //         mov     w8, #2
    //         mul     w8, w8, w9
    //         str     w8, [sp, #12]
    //         b       .LBB0_3
    // .LBB0_2:
    //         ldr     w8, [sp, #8]
    //         ldr     w9, [sp, #8]
    //         mul     w8, w8, w9
    //         str     w8, [sp, #12]
    //         b       .LBB0_3
    // .LBB0_3:
    //         ldr     w0, [sp, #12]
    //         add     sp, sp, #16
    //         ret
    // ```

    // Optimized (`-O1` or greater):
    // ```asm
    // foobar:
    //     mul     w8, w0, w0
    //     lsl     w9, w0, #1
    //     tst     w0, #0x1
    //     csel    w0, w9, w8, eq
    //     ret
    // ```
    const _FOOBAR: &[u8] =
        b"\x08\x7c\x00\x1b\x09\x78\x1f\x53\x1f\x00\x00\x72\x20\x01\x88\x1a\xc0\x03\x5f\xd6";
    // _ = simulans::disas(FOOBAR, 0);
    // Capstone output:

    const FOOBAR_UNOPT: &[u8] = b"\x02\x00\x00\x94\x17\x00\x00\x14\xff\x43\x00\xd1\xe0\x0b\x00\xb9\xe8\x0b\x40\xb9\x4a\x00\x80\x52\x09\x0d\xca\x1a\x29\x7d\x0a\x1b\x08\x01\x09\x6b\xe8\x00\x00\x35\x01\x00\x00\x14\xe9\x0b\x40\xb9\x48\x00\x80\x52\x08\x7d\x09\x1b\xe8\x0f\x00\xb9\x06\x00\x00\x14\xe8\x0b\x40\xb9\xe9\x0b\x40\xb9\x08\x7d\x09\x1b\xe8\x0f\x00\xb9\x01\x00\x00\x14\xe0\x0f\x40\xb9\xff\x43\x00\x91\xc0\x03\x5f\xd6\x1f\x20\x03\xd5";
    _ = simulans::disas(FOOBAR_UNOPT, 0);
    // Capstone output:
    // 0x0: bl #8
    // 0x4: b #0x60
    // 0x8: sub sp, sp, #0x10
    // 0xc: str w0, [sp, #8]
    // 0x10: ldr w8, [sp, #8]
    // 0x14: mov w10, #2
    // 0x18: sdiv w9, w8, w10
    // 0x1c: mul w9, w9, w10
    // 0x20: subs w8, w8, w9
    // 0x24: cbnz w8, #0x40
    // 0x28: b #0x2c
    // 0x2c: ldr w9, [sp, #8]
    // 0x30: mov w8, #2
    // 0x34: mul w8, w8, w9
    // 0x38: str w8, [sp, #0xc]
    // 0x3c: b #0x54
    // 0x40: ldr w8, [sp, #8]
    // 0x44: ldr w9, [sp, #8]
    // 0x48: mul w8, w8, w9
    // 0x4c: str w8, [sp, #0xc]
    // 0x50: b #0x54
    // 0x54: ldr w0, [sp, #0xc]
    // 0x58: add sp, sp, #0x10
    // 0x5c: ret
    // 0x60: nop
    env_logger::init();
    const MEMORY_SIZE: u64 = (4 * FOOBAR_UNOPT.len()) as u64;
    let mut machine = machine::Armv8AMachine::new(MemorySize(NonZero::new(MEMORY_SIZE).unwrap()));

    let entry_point = machine.mem.phys_offset;

    // Pass "10" as `num`
    machine.cpu_state.registers.x0 = 10;
    main_loop(&mut machine, entry_point, FOOBAR_UNOPT).unwrap();
    assert_eq!(machine.cpu_state.registers.x0, 20);
    let mut machine = machine::Armv8AMachine::new(MemorySize(NonZero::new(MEMORY_SIZE).unwrap()));

    // Pass "11" as `num`
    machine.cpu_state.registers.x0 = 11;
    main_loop(&mut machine, entry_point, FOOBAR_UNOPT).unwrap();
    assert_eq!(
        machine.cpu_state.registers.x0,
        11 * 11,
        "{:?}",
        machine.cpu_state.registers
    );
    // // Optimized
    // let mut machine = machine::Armv8AMachine::new(0x40080000 + 2 *
    // FOOBAR.len()); // Pass "10" as `num`
    // machine.cpu_state.registers.x0 = 10;
    // let _sp: i64 = unsafe { run_code(&mut machine, FOOBAR, ()).unwrap() };
    // let mut machine = machine::Armv8AMachine::new(0x40080000 + 2 *
    // FOOBAR.len()); // Pass "11" as `num`
    // machine.cpu_state.registers.x0 = 11;
    // let _sp: i64 = unsafe { run_code(&mut machine, FOOBAR, ()).unwrap() };
    // assert_eq!(machine.cpu_state.registers.x0, 22);
}
