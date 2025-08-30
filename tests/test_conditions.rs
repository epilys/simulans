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

use simulans::{cpu_state::NZCV, main_loop, memory::*};

#[macro_use]
mod utils;

#[test]
/// ```asm
/// // load a 64-bit immediate using MOV
/// .macro movq Xn, imm
///   movz    \Xn,  \imm & 0xFFFF
///   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
///   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
///   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
/// .endm
///
/// // Set and Clear NZCV field macros, equivalent C code:
/// // ```c
/// // #include <stdint.h>
/// //
/// // enum NZCVBit {
/// //   N = 31,
/// //   Z = 30,
/// //   C = 29,
/// //   V = 28,
/// // };
/// //
/// // #define CLEAR(field)                                                           \
/// //   void clear##field(void) {                                                    \
/// //     uint64_t nzcv;                                                             \
/// //     __asm volatile("mrs %0, NZCV" : "=r"(nzcv)::);                             \
/// //     nzcv &= ~(1 << (field));                                                   \
/// //     __asm volatile("msr NZCV, %0" ::"r"(nzcv) :);                              \
/// //   }
/// //
/// // #define SET(field)                                                             \
/// //   void set##field(void) {                                                      \
/// //     uint64_t nzcv;                                                             \
/// //     __asm volatile("mrs %0, NZCV" : "=r"(nzcv)::);                             \
/// //     nzcv |= 1 << (field);                                                      \
/// //     __asm volatile("msr NZCV, %0" ::"r"(nzcv) :);                              \
/// //   }
/// //
/// // #define DEF(field)                                                             \
/// //   CLEAR(field);                                                                \
/// //   SET(field);
/// //
/// // DEF(N);
/// // DEF(Z);
/// // DEF(C);
/// // DEF(V);
/// //```
///
/// .macro clearN
///   mrs     x30, NZCV
///   and     x30, x30, #0x7fffffff
///   msr     NZCV, x30
/// .endm
///
/// .macro setN
///   mrs     x30, NZCV
///   orr     x30, x30, #0xffffffff80000000
///   msr     NZCV, x30
/// .endm
///
/// .macro clearZ
///   mrs     x30, NZCV
///   and     x30, x30, #0xffffffffbfffffff
///   msr     NZCV, x30
/// .endm
///
/// .macro setZ
///   mrs     x30, NZCV
///   orr     x30, x30, #0x40000000
///   msr     NZCV, x30
/// .endm
///
/// .macro clearC
///   mrs     x30, NZCV
///   and     x30, x30, #0xffffffffdfffffff
///   msr     NZCV, x30
/// .endm
///
/// .macro setC
///   mrs     x30, NZCV
///   orr     x30, x30, #0x20000000
///   msr     NZCV, x30
/// .endm
///
/// .macro clearV
///   mrs     x30, NZCV
///   and     x30, x30, #0xffffffffefffffff
///   msr     NZCV, x30
/// .endm
///
/// .macro setV
///   mrs     x30, NZCV
///   orr     x30, x30, #0x10000000
///   msr     NZCV, x30
/// .endm
///
/// // NZCV pseudo-register layout:
/// // - N, bit [31]
/// // - Z, bit [30]
/// // - C, bit [29]
/// // - V, bit [28]
///
/// clearN
/// clearZ
/// clearC
/// clearV
///
/// movq x0, 0xF0CACC1A
/// movq x1, 0xCAFEB0BA
///
/// setZ
/// csel x2, x0, x1, eq
/// csel x3, x0, x1, ne
///
/// clearZ
/// csel x4, x0, x1, eq
/// csel x5, x0, x1, ne
///
/// setC
/// csel x6, x0, x1, cs
/// csel x7, x0, x1, cc
///
/// clearC
/// csel x8, x0, x1, cs
/// csel x9, x0, x1, cc
///
/// setN
/// csel x10, x0, x1, mi
/// csel x11, x0, x1, pl
///
/// clearN
/// csel x12, x0, x1, mi
/// csel x13, x0, x1, pl
///
/// setV
/// csel x14, x0, x1, vs
/// csel x15, x0, x1, vc
///
/// clearV
/// csel x16, x0, x1, vs
/// csel x17, x0, x1, vc
///
/// setC
/// clearZ
/// csel x18, x0, x1, hi
/// csel x19, x0, x1, ls
///
/// setN
/// setV
/// csel x20, x0, x1, ge
/// csel x21, x0, x1, lt
///
/// clearV
/// csel x22, x0, x1, ge
/// csel x23, x0, x1, lt
///
/// clearZ
/// clearN
/// csel x24, x0, x1, gt
/// csel x25, x0, x1, le
///
/// setV
/// csel x26, x0, x1, gt
/// csel x27, x0, x1, le
///
/// csel x28, x0, x1, al
/// csel x29, x0, x1, nv
/// ```
fn test_conditional_execution() {
    _ = env_logger::builder().is_test(true).try_init();

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_cond.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    // _ = simulans::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        // Initial, constant values:
        assert_hex_eq!(reg!(x0), 0xF0CACC1A);
        assert_hex_eq!(reg!(x1), 0xCAFEB0BA);

        // Results of CSEL:

        //  EQ         Equal                                A == B   Z == 1
        //  NE         Not Equal                            A != B   Z == 0
        // setZ
        // csel x2, x0, x1, eq
        // csel x3, x0, x1, ne
        assert_hex_eq!(reg!(x2), reg!(x0));
        assert_hex_eq!(reg!(x3), reg!(x1));
        // clearZ
        // csel x4, x0, x1, eq
        // csel x5, x0, x1, ne
        assert_hex_eq!(reg!(x4), reg!(x1));
        assert_hex_eq!(reg!(x5), reg!(x0));
        //  CS         Carry set                            A >= B   C == 1
        //  CC         Carry clear                          A < B    C == 0
        // setC
        // csel x6, x0, x1, cs
        // csel x7, x0, x1, cc
        assert_hex_eq!(reg!(x6), reg!(x0));
        assert_hex_eq!(reg!(x7), reg!(x1));
        // clearC
        // csel x8, x0, x1, cs
        // csel x9, x0, x1, cc
        assert_hex_eq!(reg!(x8), reg!(x1));
        assert_hex_eq!(reg!(x9), reg!(x0));
        //  MI         Minus, negative                      A < B    N == 1
        //  PL         Plus or zero                         A >= B   N == 0
        // setN
        // csel x10, x0, x1, mi
        // csel x11, x0, x1, pl
        assert_hex_eq!(reg!(x10), reg!(x0));
        assert_hex_eq!(reg!(x11), reg!(x1));
        // clearN
        // csel x12, x0, x1, mi
        // csel x13, x0, x1, pl
        assert_hex_eq!(reg!(x12), reg!(x1));
        assert_hex_eq!(reg!(x13), reg!(x0));
        //  VS         Overflow set                         -        V == 1
        //  VC         Overflow clear                       -        V == 0
        // setV
        // csel x14, x0, x1, vs
        // csel x15, x0, x1, vc
        assert_hex_eq!(reg!(x14), reg!(x0));
        assert_hex_eq!(reg!(x15), reg!(x1));
        // clearV
        // csel x16, x0, x1, vs
        // csel x17, x0, x1, vc
        assert_hex_eq!(reg!(x16), reg!(x1));
        assert_hex_eq!(reg!(x17), reg!(x0));
        //  HI         Higher                               A > B    C == 1 && Z == 0
        //  LS         Lower or same                        A <= B   !(C == 1 && Z == 0)
        // setC
        // clearZ
        // csel x18, x0, x1, hi
        // csel x19, x0, x1, ls
        assert_hex_eq!(reg!(x18), reg!(x0));
        assert_hex_eq!(reg!(x19), reg!(x1));
        //  GE         Greater than or equal                A >= B   N == V
        //  LT         Less than                            A < B    N != V
        // setN
        // setV
        // csel x20, x0, x1, ge
        // csel x21, x0, x1, lt
        assert_hex_eq!(reg!(x20), reg!(x0));
        assert_hex_eq!(reg!(x21), reg!(x1));
        // clearV
        // csel x22, x0, x1, ge
        // csel x23, x0, x1, lt
        assert_hex_eq!(reg!(x22), reg!(x1));
        assert_hex_eq!(reg!(x23), reg!(x0));
        //  GT         Greater than                         A > B    Z == 0 && N == V
        //  LE         Less than or equal                   A <= B   !(Z == 0 && N == V)
        // clearZ
        // clearN
        // csel x24, x0, x1, gt
        // csel x25, x0, x1, le
        assert_hex_eq!(reg!(x24), reg!(x0));
        assert_hex_eq!(reg!(x25), reg!(x1));
        // setV
        // csel x26, x0, x1, gt
        // csel x27, x0, x1, le
        assert_hex_eq!(reg!(x26), reg!(x1));
        assert_hex_eq!(reg!(x27), reg!(x0));
        //  AL         Always                               true     -
        //  NV         Always (Yep, "never" is a misnomer)  true     -
        // csel x28, x0, x1, al
        // csel x29, x0, x1, nv
        assert_hex_eq!(reg!(x28), reg!(x0));
        assert_hex_eq!(reg!(x29), reg!(x0));
    }
}

#[test]
/// ```asm
/// msr NZCV, xzr
///
/// movz x0, 0x1
/// movz x1, 0x2
///
/// cmp x0, x1
/// mrs x8, NZCV
/// msr NZCV, xzr
///
/// cmp x1, x0
/// mrs x9, NZCV
/// msr NZCV, xzr
///
/// cmp xzr, xzr
/// mrs x10, NZCV
/// ```
fn test_cmp_nzcv() {
    _ = env_logger::builder().is_test(true).try_init();

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_cmp.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    // _ = simulans::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        // Initial, constant values:
        assert_hex_eq!(reg!(x0), 0x1);
        assert_hex_eq!(reg!(x1), 0x2);

        {
            // Results of CMP:
            // cmp x0, x1
            // mrs x8, NZCV
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();
            // A == B
            fields.set_z(false);
            // A >= B
            fields.set_c(false);
            // A < B
            fields.set_n(true);
            fields.set_v(false);
            nzcv.set_fields(fields);

            assert_eq!(nzcv, NZCV::from(reg!(x8)));
            assert_hex_eq!(reg!(x8), nzcv.into());
        }

        {
            // msr NZCV, xzr
            // cmp x1, x0
            // mrs x9, NZCV
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();
            // A == B
            fields.set_z(false);
            // A >= B
            fields.set_c(true);
            // A < B
            fields.set_n(false);
            // Overflow
            fields.set_v(false);
            nzcv.set_fields(fields);

            assert_eq!(nzcv, NZCV::from(reg!(x9)));
            assert_hex_eq!(reg!(x9), nzcv.into());
        }

        {
            // msr NZCV, xzr
            // cmp xzr, xzr
            // mrs x10, NZCV
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();
            // A == B
            fields.set_z(true);
            // A >= B
            fields.set_c(true);
            // A < B
            fields.set_n(false);
            // Overflow
            fields.set_v(false);
            nzcv.set_fields(fields);

            assert_hex_eq!(reg!(nzcv).into(), reg!(x10));
            assert_eq!(nzcv, NZCV::from(reg!(x10)));
            assert_hex_eq!(reg!(x10), nzcv.into());
        }

        {
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();
            // A == B
            fields.set_z(false);
            // A >= B
            fields.set_c(false);
            // A < B
            fields.set_n(true);
            // Overflow
            fields.set_v(false);
            nzcv.set_fields(fields);
            assert_eq!(u64::from(nzcv) & (1 << 31), 1 << 31);
            fields.set_n(false);
            nzcv.set_fields(fields);
            assert_eq!(u64::from(nzcv) & (1 << 31), 0);
            fields.set_z(true);
            nzcv.set_fields(fields);
            assert_eq!(u64::from(nzcv) & (1 << 30), 1 << 30);
        }
    }
}
// │   0x40080078 <text_begin+120> adr x29, 0x40086000  │
// │   0x4008007c <text_begin+124> nop  │
// │   0x40080080 <text_begin+128> adr x30, 0x40086000  │
// │   0x40080084 <text_begin+132> cmp x29, x30 │
// │   0x40080088 <text_begin+136> b.cs0x40080094 <text_begin+148>  // b.hs,
// b.nlast│ │   0x4008008c <text_begin+140> stp xzr, xzr, [x29], #16 │
// │  >0x40080090 <text_begin+144> b   0x40080084 <text_begin+132>

#[test]
/// ```asm
/// // load a 64-bit immediate using MOV
/// .macro movq Xn, imm
///   movz    \Xn,  \imm & 0xFFFF
///   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
///   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
///   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
/// .endm
///
/// movq x29, 0x40086000
/// movq x30, 0x40086000
/// movz x2, #0x0
/// cmp x29, x30
/// b.cs carry_set
/// b quit
///
/// carry_set:
/// movq x2, 0x1
///
/// quit:
/// nop
/// ```
fn test_cmp_b_cnd() {
    _ = env_logger::builder().is_test(true).try_init();

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_b_cnd.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    _ = simulans::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        // Initial, constant values:
        assert_hex_eq!(reg!(x5), 0x40086000);
        assert_hex_eq!(reg!(x6), 0x40086000);

        {
            // Results of CMP:
            // cmp x5, x6
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();
            // A == B
            fields.set_z(true);
            // A >= B
            fields.set_c(true);
            // A < B
            fields.set_n(false);
            fields.set_v(false);
            nzcv.set_fields(fields);

            assert_eq!(nzcv, reg!(nzcv));
            assert_hex_eq!(reg!(nzcv).into(), nzcv.into());
        }

        {
            assert_hex_eq!(reg!(x2), 0x1);
        }
    }
}

#[test]
/// ```asm
/// // load a 64-bit immediate using MOV
/// .macro movq Xn, imm
///   movz    \Xn,  \imm & 0xFFFF
///   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
///   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
///   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
/// .endm
///
/// movq x1, 0x40095020
/// movq x2, 0x1000000
/// adds x0, x1, x2
/// cset w8, cs
/// ```
fn test_adds() {
    _ = env_logger::builder().is_test(true).try_init();

    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_adds.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    _ = simulans::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        // Initial, constant values:
        assert_hex_eq!(reg!(x1), 0x40095020);
        assert_hex_eq!(reg!(x2), 0x1000000);

        {
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();

            fields.set_z(false);
            fields.set_c(false);
            fields.set_n(false);
            fields.set_v(false);
            nzcv.set_fields(fields);

            assert_eq!(nzcv, reg!(nzcv));
            assert_hex_eq!(reg!(nzcv).into(), nzcv.into());
        }

        {
            assert_hex_eq!(reg!(x8), 0x0);
        }
    }
}
