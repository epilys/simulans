// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Utility structs for memory sizes.

use std::num::NonZero;

#[derive(Copy, Eq, PartialEq, PartialOrd, Ord, Clone)]
#[repr(transparent)]
/// A non-zero size in bytes.
pub struct MemorySize(pub NonZero<u64>);

#[allow(non_upper_case_globals)]
impl MemorySize {
    // SAFETY: value is non-zero.
    /// A KiB.
    pub const KiB: NonZero<u64> = NonZero::new(1024).unwrap();
    // SAFETY: value is non-zero.
    /// A MiB.
    pub const MiB: NonZero<u64> = NonZero::new(Self::KiB.get() * 1024).unwrap();
    // SAFETY: value is non-zero.
    /// A GiB.
    pub const GiB: NonZero<u64> = NonZero::new(Self::MiB.get() * 1024).unwrap();

    #[inline]
    /// Constructs a new size.
    pub const fn new(value: u64) -> Option<Self> {
        if value == 0 {
            return None;
        }
        Some(Self(NonZero::new(value).unwrap()))
    }

    /// Get `u64` value.
    #[inline]
    /// Unwraps the value.
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
