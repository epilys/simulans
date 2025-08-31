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

use simulans::{
    cpu_state::{ExceptionLevel, Mode, SavedProgramStatusRegister},
    main_loop,
    memory::{Address, MemorySize},
};

#[macro_use]
mod utils;

/// Test exception levels
#[test_log::test]
fn test_exception_levels() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_exception_levels.bin");
    _ = simulans::disas(TEST_INPUT, 0x40080000);

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
    machine.cpu_state.registers.sp = 4 * TEST_INPUT.len() as u64 - 4;

    let stack_pre = machine.cpu_state.registers.sp;
    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    let stack_post = machine.cpu_state.registers.sp;
    assert_eq!(stack_post, stack_pre);
    assert_eq!(machine.cpu_state.registers.hcr_el2, 0x80000018);
    assert_eq!(machine.cpu_state.registers.scr_el3, 0xd0f);
    assert_hex_eq!(machine.cpu_state.registers.elr_el1, 0x60);
    assert_hex_eq!(machine.cpu_state.registers.x0, 0x60);
}

/// Test ERET from EL1 to EL0
#[test_log::test]
fn test_eret_to_el0() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_eret_to_el0.bin");
    _ = simulans::disas(TEST_INPUT, 0x40080000);

    const MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new((4 * TEST_INPUT.len()) as u64).unwrap());
    let entry_point = Address(0);
    let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
    let mut spsr_el1 = SavedProgramStatusRegister::default();
    spsr_el1.set_M(Mode::EL0);
    machine.cpu_state.registers.spsr_el1 = spsr_el1;

    main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    assert_hex_eq!(machine.cpu_state.registers.elr_el1, 0x14);
    assert_eq!(machine.cpu_state.pstate.EL(), ExceptionLevel::EL0);
}
