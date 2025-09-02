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

pub const extern "C" fn cntfrq_el0_read(_machine: &mut crate::machine::Armv8AMachine) -> u64 {
    0x42
}

pub extern "C" fn cntp_tval_el0_write(
    _machine: &mut crate::machine::Armv8AMachine,
    _val: u64,
) -> bool {
    tracing::error!("cntp_tval_el0 {_val:X?}");
    true
}

pub extern "C" fn cntp_ctl_el0_write(
    _machine: &mut crate::machine::Armv8AMachine,
    _val: u64,
) -> bool {
    tracing::error!("cntp_ctl_el0 {_val:X?}");
    true
}
