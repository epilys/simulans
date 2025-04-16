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

mod address;
mod size;

use std::{cmp::Ordering, ffi::CString, ops::Range, os::fd::OwnedFd};

pub use address::*;
use nix::{
    errno::Errno,
    sys::{memfd, mman::ProtFlags},
};
pub use size::*;

/// Default guest physical address to load kernel code to.
pub const KERNEL_ADDRESS: usize = 0x40080000;

// Starting offset of DRAM inside the physical address space.
pub const PHYS_MEM_START: u64 = 0x40000000;

pub struct MemoryRegion {
    /// Offset from start of physical address space.
    pub phys_offset: Address,
    pub size: MemorySize,
    pub fd: OwnedFd,
    pub map: memmap2::MmapMut,
}

impl std::fmt::Debug for MemoryRegion {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("MemoryRegion")
            .field("type", &"mmap")
            .field("size", &self.size)
            .field("fd", &self.fd)
            .finish_non_exhaustive()
    }
}

impl Ord for MemoryRegion {
    fn cmp(&self, other: &Self) -> Ordering {
        let a = Range::<Address>::from(self);
        let b = Range::<Address>::from(other);
        (a.start, a.end).cmp(&(b.start, b.end))
    }
}

impl PartialOrd for MemoryRegion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for MemoryRegion {
    fn eq(&self, other: &Self) -> bool {
        use std::os::fd::AsRawFd;

        (self.phys_offset, self.size, self.fd.as_raw_fd())
            == (other.phys_offset, other.size, other.fd.as_raw_fd())
    }
}

impl Eq for MemoryRegion {}

impl From<&MemoryRegion> for Range<Address> {
    fn from(mr: &MemoryRegion) -> Self {
        let start = mr.phys_offset;
        Self {
            start,
            end: Address(start.0 + mr.size.0.get()),
        }
    }
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
            phys_offset: Address(phys_offset as u64),
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

/// A non-owning analogue of [`MemoryRegion`] that describes its characteristics
/// but does not own its memory or holds any reference to it.
pub struct MemoryRegionDescription {
    pub start_offset: Address,
    pub size: MemorySize,
}

impl From<&MemoryRegion> for MemoryRegionDescription {
    fn from(value: &MemoryRegion) -> Self {
        Self {
            start_offset: value.phys_offset,
            size: value.size,
        }
    }
}

impl MemoryRegionDescription {
    #[inline]
    pub const fn into_range(&self) -> Range<Address> {
        let start = self.start_offset;
        Range {
            start,
            end: Address(start.0 + self.size.0.get()),
        }
    }
}
