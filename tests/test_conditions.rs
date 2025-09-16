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

#[test_log::test]
fn test_conditional_execution() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_cond.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    utils::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            (nzcv) => {
                NZCV::new(
                    bilge::prelude::u28::new(0),
                    machine.cpu_state.PSTATE().NZCV(),
                )
            };
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

#[test_log::test]
fn test_cmp_nzcv() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_cmp.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    utils::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            (nzcv) => {
                NZCV::new(
                    bilge::prelude::u28::new(0),
                    machine.cpu_state.PSTATE().NZCV(),
                )
            };
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
            fields.set_Z(false);
            // A >= B
            fields.set_C(false);
            // A < B
            fields.set_N(true);
            fields.set_V(false);
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
            fields.set_Z(false);
            // A >= B
            fields.set_C(true);
            // A < B
            fields.set_N(false);
            // Overflow
            fields.set_V(false);
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
            fields.set_Z(true);
            // A >= B
            fields.set_C(true);
            // A < B
            fields.set_N(false);
            // Overflow
            fields.set_V(false);
            nzcv.set_fields(fields);

            assert_hex_eq!(reg!(nzcv).into(), reg!(x10));
            assert_eq!(nzcv, NZCV::from(reg!(x10)));
            assert_hex_eq!(reg!(x10), nzcv.into());
        }

        {
            let mut nzcv = NZCV::from(0x0);
            let mut fields = nzcv.fields();
            // A == B
            fields.set_Z(false);
            // A >= B
            fields.set_C(false);
            // A < B
            fields.set_N(true);
            // Overflow
            fields.set_V(false);
            nzcv.set_fields(fields);
            assert_eq!(u64::from(nzcv) & (1 << 31), 1 << 31);
            fields.set_N(false);
            nzcv.set_fields(fields);
            assert_eq!(u64::from(nzcv) & (1 << 31), 0);
            fields.set_Z(true);
            nzcv.set_fields(fields);
            assert_eq!(u64::from(nzcv) & (1 << 30), 1 << 30);
        }
    }
}

#[test_log::test]
fn test_cmp_b_cnd() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_b_cnd.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    utils::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            (nzcv) => {
                NZCV::new(
                    bilge::prelude::u28::new(0),
                    machine.cpu_state.PSTATE().NZCV(),
                )
            };
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
            fields.set_Z(true);
            // A >= B
            fields.set_C(true);
            // A < B
            fields.set_N(false);
            fields.set_V(false);
            nzcv.set_fields(fields);

            assert_eq!(nzcv, reg!(nzcv));
            assert_hex_eq!(reg!(nzcv).into(), nzcv.into());
        }

        {
            assert_hex_eq!(reg!(x2), 0x1);
        }
    }
}

#[test_log::test]
fn test_adds() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_adds.bin");

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());

    utils::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

    {
        macro_rules! reg {
            (nzcv) => {
                NZCV::new(
                    bilge::prelude::u28::new(0),
                    machine.cpu_state.PSTATE().NZCV(),
                )
            };
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

            fields.set_Z(false);
            fields.set_C(false);
            fields.set_N(false);
            fields.set_V(false);
            nzcv.set_fields(fields);

            assert_eq!(nzcv, reg!(nzcv));
            assert_hex_eq!(reg!(nzcv).into(), nzcv.into());
        }

        {
            assert_hex_eq!(reg!(x8), 0x0);
        }
    }
}
