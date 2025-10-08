// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use crate::memory::Address;

#[repr(C)]
#[derive(Default, Debug)]
pub struct ExclusiveMonitor {
    /// Event pseudo-register ("Wait for Event mechanism and Send event")
    pub event_register: bool,
    marked_address: Option<Address>,
}

impl ExclusiveMonitor {
    fn reservation_granule(address: Address) -> Address {
        // α = 11; 512 words.
        // Address(crate::get_bits!(address.0, off = 11, len = 64 - 11))
        address
    }

    pub fn clrex(&mut self) {
        self.marked_address.take();
    }

    fn load_excl(&mut self, address: Address) {
        self.marked_address = Some(Self::reservation_granule(address));
    }

    fn store_excl(&mut self, address: Address) -> bool {
        let reservation = Self::reservation_granule(address);
        let failed = self.marked_address != Some(reservation);
        self.marked_address.take();
        failed
    }
}

pub extern "C" fn clrex(monitor: &mut ExclusiveMonitor) {
    monitor.clrex();
}

pub extern "C" fn load_excl(monitor: &mut ExclusiveMonitor, address: Address) {
    monitor.load_excl(address);
}

pub extern "C" fn store_excl(monitor: &mut ExclusiveMonitor, address: Address) -> bool {
    monitor.store_excl(address)
}
