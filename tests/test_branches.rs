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

use simulans::{jit, run_code};

#[test]
fn test_simple_if() {
    // This code was compiled from this C function:
    // ```c
    /* Type your code here, or load an example. */
    //int foobar(int num) {
    //    if ((num / 2) == 0 ) {
    //        return 2 * num;
    //    }
    //    return num * num;
    //}
    // ```
    // Unoptimized (`-O0`) armv8-a clang assembly:
    // ```asm
    // foobar:
    //        sub     sp, sp, #16
    //        str     w0, [sp, #8]
    //        ldr     w8, [sp, #8]
    //        mov     w9, #2
    //        sdiv    w8, w8, w9
    //        cbnz    w8, LBB0_2
    //        b       LBB0_1
    // LBB0_1:
    //        ldr     w9, [sp, #8]
    //        mov     w8, #2
    //        mul     w8, w8, w9
    //        str     w8, [sp, #12]
    //        b       LBB0_3
    // LBB0_2:
    //        ldr     w8, [sp, #8]
    //        ldr     w9, [sp, #8]
    //        mul     w8, w8, w9
    //        str     w8, [sp, #12]
    //        b       LBB0_3
    // LBB0_3:
    //        ldr     w0, [sp, #12]
    //        add     sp, sp, #16
    //        ret
    // ```
    // 
    // Optimized (`-O1` or greater):
    // ```asm
    // foobar:
    //   mul     w8, w0, w0
    //   add     w9, w0, #1
    //   lsl     w10, w0, #1
    //   cmp     w9, #3
    //   csel    w0, w10, w8, lo
    //   ret
    // ```
    // const FOOBAR: &[u8] = b"\x08\x7c\x00\x1b\x09\x04\x00\x11\x0a\x78\x1f\x53\x3f\x0d\x00\x71\x40\x31\x88\x1a\xc0\x03\x5f\xd6";
    // _ = simulans::disas(FOOBAR);
    // Capstone output:
    // 0x40080000: mul w8, w0, w0
    // 0x40080004: add w9, w0, #1
    // 0x40080008: lsl w10, w0, #1
    // 0x4008000c: cmp w9, #3
    // 0x40080010: csel w0, w10, w8, lo
    // 0x40080014: ret
    const FOOBAR_UNOPT: &[u8] = b"\xff\x43\x00\xd1\xe0\x0b\x00\xb9\xe8\x0b\x40\xb9\x49\x00\x80\x52\x08\x0d\xc9\x1a\xe8\x00\x00\x35\x01\x00\x00\x14\xe9\x0b\x40\xb9\x48\x00\x80\x52\x08\x7d\x09\x1b\xe8\x0f\x00\xb9\x06\x00\x00\x14\xe8\x0b\x40\xb9\xe9\x0b\x40\xb9\x08\x7d\x09\x1b\xe8\x0f\x00\xb9\x01\x00\x00\x14\xe0\x0f\x40\xb9\xff\x43\x00\x91\xc0\x03\x5f\xd6";
    // _ = simulans::disas(FOOBAR_UNOPT);
    // Capstone output:
    // 0x40080000: sub sp, sp, #0x10
    // 0x40080004: str w0, [sp, #8]
    // 0x40080008: ldr w8, [sp, #8]
    // 0x4008000c: mov w9, #2
    // 0x40080010: sdiv w8, w8, w9
    // 0x40080014: cbnz w8, #0x40080030
    // 0x40080018: b #0x4008001c
    // 0x4008001c: ldr w9, [sp, #8]
    // 0x40080020: mov w8, #2
    // 0x40080024: mul w8, w8, w9
    // 0x40080028: str w8, [sp, #0xc]
    // 0x4008002c: b #0x40080044
    // 0x40080030: ldr w8, [sp, #8]
    // 0x40080034: ldr w9, [sp, #8]
    // 0x40080038: mul w8, w8, w9
    // 0x4008003c: str w8, [sp, #0xc]
    // 0x40080040: b #0x40080044
    // 0x40080044: ldr w0, [sp, #0xc]
    // 0x40080048: add sp, sp, #0x10
    // 0x4008004c: ret
    // env_logger::init();
    let mut machine = jit::Armv8AMachine::new(0x40080000 + 2 * FOOBAR_UNOPT.len());
    // Pass "10" as `num`
    machine.cpu_state.registers.x0 = 10;
    let _sp: i64 = unsafe { run_code(&mut machine, FOOBAR_UNOPT, ()).unwrap() };
    let mut machine = jit::Armv8AMachine::new(0x40080000 + 2 * FOOBAR_UNOPT.len());
    // Pass "11" as `num`
    machine.cpu_state.registers.x0 = 11;
    let _sp: i64 = unsafe { run_code(&mut machine, FOOBAR_UNOPT, ()).unwrap() };
    assert_eq!(machine.cpu_state.registers.x0, 22);
    // // Optimized
    // let mut machine = jit::Armv8AMachine::new(0x40080000 + 2 * FOOBAR.len());
    // // Pass "10" as `num`
    // machine.cpu_state.registers.x0 = 10;
    // let _sp: i64 = unsafe { run_code(&mut machine, FOOBAR, ()).unwrap() };
    // let mut machine = jit::Armv8AMachine::new(0x40080000 + 2 * FOOBAR.len());
    // // Pass "11" as `num`
    // machine.cpu_state.registers.x0 = 11;
    // let _sp: i64 = unsafe { run_code(&mut machine, FOOBAR, ()).unwrap() };
    // assert_eq!(machine.cpu_state.registers.x0, 22);
}
