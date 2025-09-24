// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::num::NonZero;

use simulans::{
    cpu_state::ExceptionLevel,
    main_loop,
    memory::{Address, MemorySize},
};

#[macro_use]
mod utils;

#[test_log::test]
fn test_mmu_4k() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_mmu_4k.bin");
    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new(MemorySize::MiB.get() * 1024).unwrap());
    let entry_point = Address(0x40200000);
    {
        let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
        machine.cpu_state.PSTATE_mut().set_EL(ExceptionLevel::EL1);
        // [ref:TODO]: add address translate instructions

        main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
    }
}
