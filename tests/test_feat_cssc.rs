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

// use std::num::NonZero;

// use simulans::{machine, main_loop, memory::*};

// #[macro_use]
// mod utils;

// [ref:TODO]: Neither capstone nor binja can disassemble FEAT_CSSE.
//#[test]
//fn test_feat_cssc() {
//    // ```asm
//    // // load a 64-bit immediate using MOV
//    // .macro movq Xn, imm
//    //   movz    \Xn,  \imm & 0xFFFF
//    //   movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
//    //   movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
//    //   movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
//    // .endm
//    //
//    // // load a 32-bit immediate using MOV
//    // .macro movl Wn, imm
//    //   movz    \Wn,  \imm & 0xFFFF
//    //   movk    \Wn, (\imm >> 16) & 0xFFFF, lsl 16
//    // .endm
//    //
//    // movq x0, 0xF0CACC1A
//    // movl x1, 0xBEEF
//    // abs x2, x0
//    // abs x3, x1
//    // abs x4, x2
//    // abs x5, x1
//    // cnt x6, x0
//    // cnt x7, x1
//    // ```

//    const TEST_INPUT: &[u8] =
// b"\x40\x83\x99\xd2\x40\x19\xbe\xf2\x00\x00\xc0\xf2\x00\x00\xe0\xf2\xe1\xdd\
// x97\xd2\x01\x00\xa0\xf2\x02\x20\xc0\xda\x23\x20\xc0\xda\x44\x20\xc0\xda\x25\
// x20\xc0\xda\x06\x1c\xc0\xda\x27\x1c\xc0\xda";
//    utils::disas(TEST_INPUT, 0);
//    // Capstone output:
//    // 0x0: mov x0, #0xcc1a
//    // 0x4: movk x0, #0xf0ca, lsl #16
//    // 0x8: movk x0, #0, lsl #32
//    // 0xc: movk x0, #0, lsl #48
//    // 0x10: mov x1, #0xbeef
//    // 0x14: movk x1, #0, lsl #16
//    const MEMORY_SIZE: MemorySize =
//        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
//    let entry_point = Address(0);
//    let memory = MemoryMap::builder(MEMORY_SIZE)
//        .with_region(MemoryRegion::new("ram", MEMORY_SIZE,
// entry_point).unwrap())        .unwrap()
//        .build();
//    let mut machine = machine::Armv8AMachine::new(memory);

//    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
//    assert_hex_eq!(machine.cpu_state.registers.x1, 0xbeef);
//    assert_hex_eq!(machine.cpu_state.registers.x0, 0xf0cacc1a);
//}
