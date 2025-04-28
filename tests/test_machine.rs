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

use flat_device_tree as fdt;
use simulans::memory::*;

#[test]
fn test_fdt_generation() {
    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new(MemorySize::MiB.get() * 4).unwrap());
    let entry_point = Address(0);
    let dram = MemoryRegion::new("ram", MEMORY_SIZE, entry_point).unwrap();
    let fdt = simulans::fdt::FdtBuilder::new(&dram, MEMORY_SIZE)
        .unwrap()
        .num_vcpus(NonZero::new(1).unwrap())
        .cmdline(None)
        .build()
        .unwrap();
    let fdt = fdt::Fdt::new(&fdt.bytes).unwrap();
    dbg!(&fdt);
    eprintln!(
        "This is a devicetree representation of a {}",
        fdt.root().unwrap().model()
    );
    eprintln!(
        "...which is compatible with at least: {}",
        fdt.root().unwrap().compatible().first().unwrap()
    );
    eprintln!("...and has {} CPU(s)", fdt.cpus().count());
    eprintln!(
        "...and has at least one memory location at: {:#X}\n",
        fdt.memory()
            .unwrap()
            .regions()
            .next()
            .unwrap()
            .starting_address as usize
    );

    for node in fdt.all_nodes() {
        eprintln!(
            "{}: {:?}",
            node.name,
            node.compatible()
                .map(flat_device_tree::standard_nodes::Compatible::first),
        );
        for range in node.reg() {
            eprintln!(
                "  {:#018x?}, length {:?}",
                range.starting_address, range.size
            );
        }
    }
}
