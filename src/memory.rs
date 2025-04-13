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

use std::{ffi::CString, os::fd::OwnedFd};

use nix::{
    errno::Errno,
    sys::{memfd, mman::ProtFlags},
};

/// Default guest physical address to load kernel code to.
pub const KERNEL_ADDRESS: usize = 0x40080000;

// Starting offset of DRAM inside the physical address space.
pub const PHYS_MEM_START: u64 = 0x00000000;

pub struct MemoryRegion {
    pub size: usize,
    pub fd: OwnedFd,
    pub map: memmap2::MmapMut,
}

impl MemoryRegion {
    pub fn new(name: &str, size: u64) -> Result<Self, Errno> {
        let name = CString::new(name).unwrap();
        let fd = memfd::memfd_create(&name, memfd::MemFdCreateFlag::MFD_CLOEXEC)?;
        nix::unistd::ftruncate(&fd, size.try_into().unwrap())?;
        let mut map = unsafe { memmap2::MmapOptions::new().map_mut(&fd).unwrap() };
        unsafe {
            nix::sys::mman::mprotect(
                std::ptr::NonNull::new(map.as_mut_ptr().cast::<core::ffi::c_void>()).unwrap(),
                size.try_into().unwrap(),
                ProtFlags::PROT_READ | ProtFlags::PROT_WRITE | ProtFlags::PROT_EXEC,
            )?;
        }
        #[cfg(target_os = "linux")]
        {
            // Don't include VM memory in dumped core files.
            _ = map.advise(memmap2::Advice::DontDump);
        }
        let size: usize = size.try_into().map_err(|_| Errno::ERANGE)?;
        debug_assert_eq!(map.len(), size);
        Ok(Self { size, fd, map })
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.size
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
