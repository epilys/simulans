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

/// Test a simple function that squares its input.
#[test]
fn test_square() {
    // This code was compiled from this C function:
    // ```c
    //  int square(int num) {
    //    return num * num;
    //  }
    // ```
    const SQUARED: &[u8] = b"\xff\x43\x00\xd1\xe0\x0f\x00\xb9\xe8\x0f\x40\xb9\xe9\x0f\x40\xb9\x00\x7d\x09\x1b\xff\x43\x00\x91\xc0\x03\x5f\xd6";
    // Capstone disassembly:
    //
    // ```text
    // 0x40080000: sub sp, sp, #0x10
    // 0x40080004: str w0, [sp, #0xc]
    // 0x40080008: ldr w8, [sp, #0xc]
    // 0x4008000c: ldr w9, [sp, #0xc]
    // 0x40080010: mul w0, w8, w9
    // 0x40080014: add sp, sp, #0x10
    // 0x40080018: ret
    // ```
    let mut machine = jit::Armv8AMachine::default();
    let stack_pre = machine.cpu_state.registers.sp_el0;
    // Pass "25" as `num`
    machine.cpu_state.registers.x0 = 25;
    let _sp: i64 = unsafe { run_code(&mut machine, SQUARED, ()).unwrap() };
    assert_eq!(machine.cpu_state.registers.x0, 625);
    assert_eq!(machine.cpu_state.registers.x8, 25);
    assert_eq!(machine.cpu_state.registers.x9, 25);
    let stack_post = machine.cpu_state.registers.sp_el0;
    assert_eq!(stack_post, stack_pre);
}

/// Test a str and a load from the stack
#[test]
fn test_load_stores() {
    // Capstone output:
    // 0x40080000: str x0, [sp, #-0x10]!
    // 0x40080004: ldr x1, [sp], #0x10
    const LOAD_STORES: &[u8] = b"\xe0\x0f\x1f\xf8\xe1\x07\x41\xf8";
    // _ = simulans::disas(LOAD_STORES);

    let mut machine = jit::Armv8AMachine::default();
    let stack_pre = machine.cpu_state.registers.sp_el0;
    machine.cpu_state.registers.x0 = 0xbadbeef;
    let _: i64 = unsafe { run_code(&mut machine, LOAD_STORES, ()).unwrap() };
    let stack_end = machine.stack.data.len() - 1;
    assert_eq!(machine.stack.data[stack_end - 0x10], 0xef);
    assert_eq!(machine.stack.data[stack_end - 0x10 + 1], 0xbe);
    assert_eq!(machine.stack.data[stack_end - 0x10 + 2], 0xad);
    assert_eq!(machine.stack.data[stack_end - 0x10 + 3], 0x0b);
    assert_eq!(machine.cpu_state.registers.x0, 0xbadbeef);
    assert_eq!(machine.cpu_state.registers.x1, 0xbadbeef);
    let stack_post = machine.cpu_state.registers.sp_el0;
    assert_eq!(stack_post, stack_pre);
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
    // _ = simulans::disas(STACK_ADD);

    let mut machine = jit::Armv8AMachine::default();
    let stack_pre = machine.cpu_state.registers.sp_el0;
    machine.cpu_state.registers.x0 = 0xbadbeef;
    let _: i64 = unsafe { run_code(&mut machine, STACK_ADD, ()).unwrap() };
    let stack_post = machine.cpu_state.registers.sp_el0;
    assert_eq!(stack_post, stack_pre);
    assert_eq!(machine.cpu_state.registers.x0, 2 * 0x1234);
    assert_eq!(machine.cpu_state.registers.x1, 0x1234);
    let stack_end = machine.stack.data.len() - 1;
    assert_eq!(machine.stack.data[stack_end - 0x10], 0x34);
    assert_eq!(machine.stack.data[stack_end - 0x10 + 1], 0x12);
}
