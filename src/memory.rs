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

#![allow(clippy::len_without_is_empty)]

use std::{ffi::CString, num::NonZero, os::fd::OwnedFd};

use nix::{
    errno::Errno,
    sys::{memfd, mman::ProtFlags},
};

/// Default guest physical address to load kernel code to.
pub const KERNEL_ADDRESS: usize = 0x40080000;

// Starting offset of DRAM inside the physical address space.
pub const PHYS_MEM_START: u64 = 0x40000000;

pub struct MemoryRegion {
    /// Offset from start of physical address space.
    pub phys_offset: usize,
    pub size: MemorySize,
    pub fd: OwnedFd,
    pub map: memmap2::MmapMut,
}

impl MemoryRegion {
    pub fn new(name: &str, size: MemorySize, phys_offset: usize) -> Result<Self, Errno> {
        let name = CString::new(name).unwrap();
        let fd = memfd::memfd_create(&name, memfd::MemFdCreateFlag::MFD_CLOEXEC)?;
        nix::unistd::ftruncate(&fd, size.get().try_into().unwrap())?;
        // SAFETY: `fd` is a valid file descriptor.
        let mut map = unsafe { memmap2::MmapOptions::new().map_mut(&fd).unwrap() };
        // SAFETY: `map`'s pointer is a valid memory address pointer of size `size`.
        unsafe {
            nix::sys::mman::mprotect(
                std::ptr::NonNull::new(map.as_mut_ptr().cast::<core::ffi::c_void>()).unwrap(),
                size.get().try_into().unwrap(),
                ProtFlags::PROT_READ | ProtFlags::PROT_WRITE | ProtFlags::PROT_EXEC,
            )?;
        }
        #[cfg(target_os = "linux")]
        {
            // Don't include VM memory in dumped core files.
            _ = map.advise(memmap2::Advice::DontDump);
        }
        let u_size: usize = size.get().try_into().map_err(|_| Errno::ERANGE)?;
        debug_assert_eq!(map.len(), u_size);
        Ok(Self {
            phys_offset,
            size,
            fd,
            map,
        })
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.size.get() as usize
    }
}

#[derive(Copy, Clone)]
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

#[derive(Copy, Clone)]
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
