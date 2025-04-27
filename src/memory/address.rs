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

use std::ops::{Add, AddAssign, Sub, SubAssign};

use crate::memory::MemorySize;

#[derive(Copy, Clone, Ord, Eq, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Address(pub u64);

impl std::fmt::Display for Address {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "0x{:x}", self.0)
    }
}

impl std::fmt::Debug for Address {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "0x{:x}", self.0)
    }
}

impl Add for Address {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        Self(self.0.checked_add(other.0).unwrap())
    }
}

impl Add<u64> for Address {
    type Output = Self;

    fn add(self, other: u64) -> Self::Output {
        Self(self.0.checked_add(other).unwrap())
    }
}

impl Add<usize> for Address {
    type Output = Self;

    fn add(self, other: usize) -> Self::Output {
        Self(self.0.checked_add(u64::try_from(other).unwrap()).unwrap())
    }
}

impl Add<MemorySize> for Address {
    type Output = Self;

    fn add(self, other: MemorySize) -> Self::Output {
        Self(self.0.checked_add(other.get()).unwrap())
    }
}

impl AddAssign for Address {
    fn add_assign(&mut self, other: Self) {
        self.0 = self.0.checked_add(other.0).unwrap();
    }
}

impl AddAssign<u64> for Address {
    fn add_assign(&mut self, other: u64) {
        self.0 = self.0.checked_add(other).unwrap();
    }
}

impl AddAssign<usize> for Address {
    fn add_assign(&mut self, other: usize) {
        self.0 = self.0.checked_add(u64::try_from(other).unwrap()).unwrap();
    }
}

impl AddAssign<MemorySize> for Address {
    fn add_assign(&mut self, other: MemorySize) {
        self.0 = self.0.checked_add(other.get()).unwrap();
    }
}

impl Sub for Address {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        Self(self.0.checked_sub(other.0).unwrap())
    }
}

impl Sub<u64> for Address {
    type Output = Self;

    fn sub(self, other: u64) -> Self::Output {
        Self(self.0.checked_sub(other).unwrap())
    }
}

impl Sub<usize> for Address {
    type Output = Self;

    fn sub(self, other: usize) -> Self::Output {
        Self(self.0.checked_sub(u64::try_from(other).unwrap()).unwrap())
    }
}

impl Sub<MemorySize> for Address {
    type Output = Self;

    fn sub(self, other: MemorySize) -> Self::Output {
        Self(self.0.checked_sub(other.get()).unwrap())
    }
}

impl SubAssign for Address {
    fn sub_assign(&mut self, other: Self) {
        self.0 = self.0.checked_sub(other.0).unwrap();
    }
}

impl SubAssign<u64> for Address {
    fn sub_assign(&mut self, other: u64) {
        self.0 = self.0.checked_sub(other).unwrap();
    }
}

impl SubAssign<usize> for Address {
    fn sub_assign(&mut self, other: usize) {
        self.0 = self.0.checked_sub(u64::try_from(other).unwrap()).unwrap();
    }
}

impl SubAssign<MemorySize> for Address {
    fn sub_assign(&mut self, other: MemorySize) {
        self.0 = self.0.checked_sub(other.get()).unwrap();
    }
}
