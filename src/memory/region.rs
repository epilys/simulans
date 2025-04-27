//
// simulans
//
// Copyright 2025 Emmanouil Pitsidianakis <manos@pitsidianak.is>
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

use std::{cmp::Ordering, ffi::CString, ops::Range, os::fd::OwnedFd};

use nix::{
    errno::Errno,
    sys::{memfd, mman::ProtFlags},
};

use crate::memory::{Address, MemorySize, Width};

pub struct MmappedMemory {
    pub fd: OwnedFd,
    pub map: memmap2::MmapMut,
    pub read_only: bool,
}

impl std::fmt::Debug for MmappedMemory {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("MmappedMemory")
            .field("fd", &self.fd)
            .field("read_only", &self.read_only)
            .finish_non_exhaustive()
    }
}

pub trait DeviceMemoryOps: std::fmt::Debug {
    fn id(&self) -> u64;
    fn read(&self, address_inside_region: u64, width: Width) -> u64;
    fn write(&self, address_inside_region: u64, value: u64, width: Width);
}

impl PartialEq for &dyn DeviceMemoryOps {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for &dyn DeviceMemoryOps {}

#[derive(Debug)]
pub enum MemoryBacking {
    Mmap(MmappedMemory),
    Device(Box<dyn DeviceMemoryOps>),
}

impl PartialEq for MemoryBacking {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Mmap(ref a), Self::Mmap(ref b)) => a == b,
            (Self::Device(ref a), Self::Device(ref b)) => a.id() == b.id(),
            _ => false,
        }
    }
}

impl Eq for MemoryBacking {}

impl PartialEq for MmappedMemory {
    fn eq(&self, other: &Self) -> bool {
        use std::os::fd::AsRawFd;

        self.fd.as_raw_fd() == other.fd.as_raw_fd()
    }
}

impl Eq for MmappedMemory {}

pub struct MemoryRegion {
    /// Offset from start of physical address space.
    pub phys_offset: Address,
    pub size: MemorySize,
    pub backing: MemoryBacking,
}

impl std::fmt::Debug for MemoryRegion {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("MemoryRegion")
            .field("phys_offset", &self.phys_offset)
            .field("size", &self.size)
            .field("backing", &self.backing)
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
        (self.phys_offset, self.size, &self.backing)
            == (other.phys_offset, other.size, &other.backing)
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
    /// Returns a memory region backed by an `mmap(2)` created area.
    pub fn new(name: &str, size: MemorySize, phys_offset: Address) -> Result<Self, Errno> {
        if size.get().checked_add(phys_offset.0).is_none() {
            return Err(Errno::E2BIG);
        }
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
            backing: MemoryBacking::Mmap(MmappedMemory {
                fd,
                map,
                read_only: false,
            }),
        })
    }

    pub fn new_io(
        size: MemorySize,
        phys_offset: Address,
        ops: Box<dyn DeviceMemoryOps>,
    ) -> Result<Self, Errno> {
        if size.get().checked_add(phys_offset.0).is_none() {
            return Err(Errno::E2BIG);
        }
        Ok(Self {
            phys_offset,
            size,
            backing: MemoryBacking::Device(ops),
        })
    }

    #[inline]
    pub const fn len(&self) -> usize {
        self.size.get() as usize
    }

    #[inline]
    pub const fn start_addr(&self) -> Address {
        self.phys_offset
    }

    #[inline]
    pub const fn last_addr(&self) -> Address {
        if cfg!(debug_assertions) {
            return Address(
                self.phys_offset
                    .0
                    .checked_add(self.size.0.get())
                    .expect("Overflow when calculating last_addr"),
            );
        }
        Address(self.phys_offset.0 + self.size.0.get())
    }

    #[inline]
    pub const fn as_mmap(&self) -> Option<&MmappedMemory> {
        if let MemoryBacking::Mmap(ref inner) = self.backing {
            return Some(inner);
        }
        None
    }

    #[inline]
    pub const fn as_mmap_mut(&mut self) -> Option<&mut MmappedMemory> {
        if let MemoryBacking::Mmap(ref mut inner) = self.backing {
            return Some(inner);
        }
        None
    }
}

/// A non-owning analogue of [`MemoryRegion`] that describes its characteristics
/// but does not own its memory or holds any reference to it.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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

pub mod ops {
    use super::*;

    macro_rules! def_op {
        (write $fn:ident: $size:ty) => {
            pub extern "C" fn $fn(
                mem_region: &mut MemoryRegion,
                address_inside_region: u64,
                value: $size,
            ) {
                log::trace!(
                    "writing {} value {} to address {}",
                    stringify!($size),
                    value,
                    Address(address_inside_region)
                );
                match mem_region.backing {
                    MemoryBacking::Mmap(MmappedMemory { ref mut map, .. }) => {
                        let destination =
                        // SAFETY: when resolving the guest address to a memory region, we
                        // essentially performed a bounds check so we know this offset is valid.
                            unsafe { map.as_mut_ptr().add(address_inside_region as usize) };
                        // SAFETY: this is safe as long as $size width does not exceed the map's
                        // size. We don't check for this, so FIXME
                        unsafe { std::ptr::write_unaligned(destination.cast::<$size>(), value) };
                    }
                    MemoryBacking::Device(ref ops) => {
                        ops.write(
                            address_inside_region,
                            u64::from(value),
                            match std::mem::size_of::<$size>() {
                                1 => Width::_8,
                                2 => Width::_16,
                                4 => Width::_32,
                                8 => Width::_64,
                                16 => Width::_128,
                                _ => unreachable!(),
                            },
                        );
                    }
                }
            }
        };
        (read $fn:ident: $size:ty) => {
            pub extern "C" fn $fn(
                mem_region: &mut MemoryRegion,
                address_inside_region: u64,
            ) -> $size {
                log::trace!(
                    "reading {} value from address {} (inside offset = {})",
                    stringify!($size),
                    mem_region.phys_offset + Address(address_inside_region),
                    Address(address_inside_region)
                );
                match mem_region.backing {
                    MemoryBacking::Mmap(MmappedMemory { ref map, .. }) => {
                        let destination =
                        // SAFETY: when resolving the guest address to a memory region, we
                        // essentially performed a bounds check so we know this offset is valid.
                            unsafe { map.as_ptr().add(address_inside_region as usize) };
                        let value =
                        // SAFETY: this is safe as long as $size width does not exceed the map's
                        // size. We don't check for this, so FIXME
                            unsafe { std::ptr::read_unaligned(destination.cast::<$size>()) };
                        log::trace!(
                            "{}: read {} value {}=0x{:x}=0b{:b}",
                            Address(address_inside_region),
                            stringify!($size),
                            value,
                            value,
                            value,
                        );
                        value
                    }
                    MemoryBacking::Device(ref ops) => ops.read(
                        address_inside_region,
                        match std::mem::size_of::<$size>() {
                            1 => Width::_8,
                            2 => Width::_16,
                            4 => Width::_32,
                            8 => Width::_64,
                            16 => Width::_128,
                            _ => unreachable!(),
                        },
                    ) as $size,
                }
            }
        };
    }

    def_op! { write memory_region_write_8: u8 }
    def_op! { write memory_region_write_16: u16 }
    def_op! { write memory_region_write_32: u32 }
    def_op! { write memory_region_write_64: u64 }

    def_op! { read memory_region_read_8: u8 }
    def_op! { read memory_region_read_16: u16 }
    def_op! { read memory_region_read_32: u32 }
    def_op! { read memory_region_read_64: u64 }

    pub extern "C" fn memory_region_write_128(
        _mem_region: &mut MemoryRegion,
        _address_inside_region: u64,
        _value_hi: u64,
        _value_lo: u64,
    ) {
        todo!()
        // let destination = unsafe {
        //     mem_region
        //         .map
        //         .as_mut_ptr()
        //         .add(address_inside_region as usize)
        // };
        // unsafe {
        //     *destination.cast::<u128>() = value;
        // }
    }

    pub extern "C" fn memory_region_read_128(
        _mem_region: &MemoryRegion,
        _address_inside_region: u64,
    ) -> u64 {
        todo!()
        // let destination = unsafe {
        // mem_region.map.as_ptr().add(address_inside_region as usize) };
        // unsafe { *destination.cast::<u64>() }
    }
}
