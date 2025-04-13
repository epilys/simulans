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

use simulans::{machine, main_loop, memory::KERNEL_ADDRESS};

#[test]
fn test_sdiv() {
    // Capstone output:
    // 0x40080000: sub sp, sp, #0x10
    // 0x40080004: str w0, [sp, #8]
    // 0x40080008: ldr w8, [sp, #8]
    // 0x4008000c: mov w9, #2
    // 0x40080010: sdiv w8, w8, w9
    const SDIV: &[u8] =
        b"\xff\x43\x00\xd1\xe0\x0b\x00\xb9\xe8\x0b\x40\xb9\x49\x00\x80\x52\x08\x0d\xc9\x1a";
    _ = simulans::disas(SDIV);

    let mut machine = machine::Armv8AMachine::new(0x40080000 + 2 * SDIV.len() as u64);
    let stack_pre = machine.cpu_state.registers.sp;
    machine.cpu_state.registers.x0 = 11;
    main_loop(&mut machine, KERNEL_ADDRESS, SDIV).unwrap();
    let stack_post = machine.cpu_state.registers.sp;
    assert_eq!(stack_post, stack_pre - 0x10);
    assert_eq!(machine.cpu_state.registers.x8, 5);
    assert_eq!(machine.cpu_state.registers.x9, 2);
    assert_eq!(
        machine.mem.map.as_ref()[stack_post as usize - 0x10 + 0x18],
        11
    );
}
