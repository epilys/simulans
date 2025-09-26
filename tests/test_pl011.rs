// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::num::NonZero;

use simulans::{
    devices::Device,
    machine::Armv8AMachine,
    main_loop,
    memory::{Address, MemoryMap, MemoryRegion, MemorySize},
};

#[macro_use]
mod utils;

#[test_log::test]
fn test_uart_write_str() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_write_str.bin");

    const DRAM_MEMORY_SIZE: MemorySize =
        MemorySize(NonZero::new(4 * TEST_INPUT.len() as u64).unwrap());
    utils::disas(TEST_INPUT, 0);
    let entry_point = Address(0);
    let pl011_addr = Address(4 * TEST_INPUT.len() as u64);
    {
        let pl011 = simulans::devices::pl011::PL011State::new(0, pl011_addr);
        let tube = simulans::devices::tube::Tube::new(0, Address(0x0d800020));
        let memory = MemoryMap::builder()
            .with_region(MemoryRegion::new("ram", DRAM_MEMORY_SIZE, entry_point).unwrap())
            .unwrap()
            .with_region(pl011.into_memory_regions().pop().unwrap())
            .unwrap()
            .with_region(tube.into_memory_regions().pop().unwrap())
            .unwrap()
            .build();
        let mut machine = Armv8AMachine::new(memory, Default::default());
        machine.cpu_state.registers.x0 = pl011_addr.0;
        machine.cpu_state.registers.x2 = "Hello world\n".len() as u64;

        main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        assert_hex_eq!(reg!(x0), 0x0);
    }
}
