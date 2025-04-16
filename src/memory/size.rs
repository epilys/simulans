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

#[derive(Copy, Eq, PartialEq, PartialOrd, Ord, Clone)]
#[repr(transparent)]
pub struct MemorySize(pub NonZero<u64>);

#[allow(non_upper_case_globals)]
impl MemorySize {
    // SAFETY: value is non-zero.
    pub const KiB: NonZero<u64> = NonZero::new(1024).unwrap();
    // SAFETY: value is non-zero.
    pub const MiB: NonZero<u64> = NonZero::new(Self::KiB.get() * 1024).unwrap();
    // SAFETY: value is non-zero.
    pub const GiB: NonZero<u64> = NonZero::new(Self::MiB.get() * 1024).unwrap();

    /// Get `u64` value.
    #[inline]
    pub const fn get(self) -> u64 {
        self.0.get()
    }
}

impl std::fmt::Display for MemorySize {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let bytes = self.get();
        if bytes == 0 {
            write!(fmt, "0")
        } else if bytes < Self::KiB.get() {
            write!(fmt, "{}bytes", bytes)
        } else if bytes < Self::MiB.get() {
            write!(fmt, "{}KiB", bytes / Self::KiB)
        } else if bytes < Self::GiB.get() {
            write!(fmt, "{}MiB", bytes / Self::MiB)
        } else {
            write!(fmt, "{}GiB", bytes / Self::GiB)
        }
    }
}

impl std::fmt::Debug for MemorySize {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let bytes = self.get();
        if bytes == 0 {
            write!(fmt, "0")
        } else if bytes < Self::KiB.get() {
            write!(fmt, "{}bytes", bytes)
        } else if bytes < Self::MiB.get() {
            write!(fmt, "{}KiB", bytes / Self::KiB)
        } else if bytes < Self::GiB.get() {
            write!(fmt, "{}MiB", bytes / Self::MiB)
        } else {
            write!(fmt, "{}GiB", bytes / Self::GiB)
        }
    }
}
