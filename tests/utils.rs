//
// simulans
//
// Copyright 2025 Emmanouil Pitsidianakis <manos@pitsidianak.is>
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

use std::{
    pin::Pin,
    sync::{atomic::AtomicU8, Arc},
};

use simulans::{
    devices::Device,
    machine::Armv8AMachine,
    memory::{Address, MemoryMap, MemoryRegion, MemorySize},
};

#[macro_export]
macro_rules! assert_hex_eq {
    ($left: expr, $right: expr$(,)?) => {{
        let left: u64 = $left;
        let right: u64 = $right;
        assert_eq!(
            left,
            right,
            "Comparing {left_s} with {right_s} failed:\n0x{left:032x} {left_s}\n0x{right:032x} \
             {right_s}\n0b{left:064b} {left_s}\n0b{right:064b} {right_s}",
            left_s = stringify!($left),
            right_s = stringify!($right),
            left = left,
            right = right,
        );
    }};
}

#[allow(dead_code)]
pub fn make_test_machine(
    memory_size: MemorySize,
    memory_start: Address,
) -> Pin<Box<Armv8AMachine>> {
    let exit_request = Arc::new(AtomicU8::new(0));
    let tube = simulans::devices::tube::Tube::new(0, Arc::clone(&exit_request));
    let mut memory = MemoryMap::builder()
        .with_region(MemoryRegion::new("ram", memory_size, memory_start).unwrap())
        .unwrap();

    memory
        .add_region(
            MemoryRegion::new_io(
                MemorySize::new(0x100).unwrap(),
                Address(0x0d800020),
                tube.ops(),
            )
            .unwrap(),
        )
        .unwrap();
    let memory = memory.build();
    Armv8AMachine::new_with_exit_request(memory, exit_request)
}
