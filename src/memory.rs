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

use nix::{errno::Errno, sys::memfd};

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
        let map = unsafe { memmap2::MmapOptions::new().map_mut(&fd).unwrap() };
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
