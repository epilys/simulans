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
    // This code was compiled from this C function:
    // ```c
    // int foobar(int num) {
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
    const FOOBAR: &[u8] = include_bytes!("./inputs/test_simple_if_opt.bin");
    // _ = simulans::disas(FOOBAR, 0);
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
            assert_eq!(machine.cpu_state.registers.x0, 20);
        }
        {
            let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

            // Pass "11" as `num`
            machine.cpu_state.registers.x0 = 11;
            machine.cpu_state.registers.sp = 4 * FOOBAR_UNOPT.len() as u64 - 4;
            main_loop(&mut machine, entry_point, FOOBAR_UNOPT).unwrap();
            assert_eq!(
                machine.cpu_state.registers.x0,
                11 * 11,
                "{:?}",
                machine.cpu_state.registers
            );
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
            assert_eq!(machine.cpu_state.registers.x0, 20);
        }
        {
            let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

            // Pass "11" as `num`
            machine.cpu_state.registers.x0 = 11;
            machine.cpu_state.registers.sp = 4 * FOOBAR.len() as u64 - 4;
            main_loop(&mut machine, entry_point, FOOBAR).unwrap();
            assert_eq!(
                machine.cpu_state.registers.x0,
                11 * 11,
                "{:?}",
                machine.cpu_state.registers
            );
        }
    }
}
