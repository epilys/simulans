// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::{num::NonZero, sync::Arc};

use simulans::{
    devices::Device,
    machine::{Armv8AMachine, CharBackend},
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
        let buffer = Default::default();
        let char_backend = CharBackend::new_sink(Arc::clone(&buffer));
        let interrupts = Default::default();
        let mut memory_builder = MemoryMap::builder()
            .with_region(MemoryRegion::new("ram", DRAM_MEMORY_SIZE, entry_point).unwrap())
            .unwrap();
        let pl011 = simulans::devices::pl011::PL011State::new(
            memory_builder.device_registry().register(),
            pl011_addr,
            char_backend.writer.clone(),
            &interrupts,
        );
        let tube = simulans::devices::tube::Tube::new(
            memory_builder.device_registry().register(),
            Address(0x0d800020),
        );
        let memory = memory_builder
            .with_region(pl011.into_memory_regions().pop().unwrap())
            .unwrap()
            .with_region(tube.into_memory_regions().pop().unwrap())
            .unwrap()
            .build();
        let mut machine = Armv8AMachine::new(memory, char_backend, interrupts);
        machine.cpu_state.registers.x0 = pl011_addr.0;
        machine.cpu_state.registers.x2 = "Hello world\n".len() as u64;

        main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();

        macro_rules! reg {
            ($reg:ident) => {
                machine.cpu_state.registers.$reg
            };
        }

        assert_hex_eq!(reg!(x0), 0x0);

        assert_eq!(buffer.lock().unwrap().as_slice(), b"Hello world\n");
    }
}
