// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Memory region types

#![allow(clippy::len_without_is_empty)]

use std::{cmp::Ordering, ops::Range, path::PathBuf};

#[cfg(target_os = "linux")]
mod linux;
#[cfg(target_os = "macos")]
mod macos;

#[cfg(target_os = "linux")]
pub use linux::MmappedMemory;
#[cfg(target_os = "macos")]
pub use macos::MmappedMemory;
use nix::errno::Errno;

use crate::{
    devices::DeviceOps,
    memory::{Address, MemorySize, Width},
};

#[derive(Debug)]
/// Kind of memory backing.
pub enum MemoryBacking {
    /// A mmapped region.
    Mmap(MmappedMemory),
    /// Device memory.
    Device((u64, Box<dyn DeviceOps>)),
}

impl PartialEq for MemoryBacking {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Mmap(ref a), Self::Mmap(ref b)) => a == b,
            (Self::Device((ref id_a, ref a)), Self::Device((ref id_b, ref b))) => {
                (id_a, a.id()) == (id_b, b.id())
            }
            _ => false,
        }
    }
}

impl Eq for MemoryBacking {}

/// A virtual machine memory region.
pub struct MemoryRegion {
    /// Offset from start of physical address space.
    pub phys_offset: Address,
    /// Size in bytes.
    pub size: MemorySize,
    /// The backing.
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
            tracing::error!("Size {size} cannot fit to offset {phys_offset}, it overflows.");
            return Err(Errno::E2BIG);
        }
        Ok(Self {
            phys_offset,
            size,
            backing: super::MemoryBacking::Mmap(MmappedMemory::new_region(name, size)?),
        })
    }

    #[cfg(target_os = "macos")]
    /// Creates a new file-backed mmapped memory region, returns `ENOTSUP` for
    /// macos.
    pub fn new_file(
        _name: &str,
        _path: PathBuf,
        _size: MemorySize,
        _phys_offset: Address,
    ) -> Result<Self, Errno> {
        Err(Errno::ENOTSUP)
    }

    #[cfg(not(target_os = "macos"))]
    /// Creates a new file-backed mmapped memory region.
    pub fn new_file(
        name: &str,
        path: PathBuf,
        size: MemorySize,
        phys_offset: Address,
    ) -> Result<Self, Errno> {
        if size.get().checked_add(phys_offset.0).is_none() {
            return Err(Errno::E2BIG);
        }
        Ok(Self {
            phys_offset,
            size,
            backing: super::MemoryBacking::Mmap(MmappedMemory::new_file_region(name, path, size)?),
        })
    }

    /// Creates a new I/O memory region.
    pub fn new_io(
        size: MemorySize,
        phys_offset: Address,
        id: u64,
        ops: Box<dyn DeviceOps>,
    ) -> Result<Self, Errno> {
        if size.get().checked_add(phys_offset.0).is_none() {
            return Err(Errno::E2BIG);
        }
        Ok(Self {
            phys_offset,
            size,
            backing: MemoryBacking::Device((id, ops)),
        })
    }

    #[inline]
    /// Returns the size in bytes.
    pub const fn len(&self) -> usize {
        self.size.get() as usize
    }

    #[inline]
    /// Returns the first address covered by this region.
    pub const fn start_addr(&self) -> Address {
        self.phys_offset
    }

    #[inline]
    /// Returns the last address covered by this region.
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
    /// Returns reference to device memory.
    pub fn as_device(&self) -> Option<(u64, &dyn DeviceOps)> {
        if let MemoryBacking::Device((ref id, ref inner)) = self.backing {
            return Some((*id, inner.as_ref()));
        }
        None
    }

    #[inline]
    /// Returns reference to mmapped memory.
    pub const fn as_mmap(&self) -> Option<&MmappedMemory> {
        if let MemoryBacking::Mmap(ref inner) = self.backing {
            return Some(inner);
        }
        None
    }

    #[inline]
    /// Returns mutable reference to mmapped memory.
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
    /// Start offset in memory map.
    pub start_offset: Address,
    /// Region size.
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
    /// Returns a [`Range<Address>`] for this description.
    pub const fn into_range(&self) -> Range<Address> {
        let start = self.start_offset;
        Range {
            start,
            end: Address(start.0 + self.size.0.get()),
        }
    }
}

pub mod ops {
    //! Helper memory I/O functions for JIT code.

    use super::*;
    use crate::{cpu_state::ExitRequest, tracing};

    macro_rules! def_op {
        (write $fn:ident: $size:ty) => {
            impl MemoryRegion {
                pub fn $fn(
                    &mut self,
                    address_inside_region: u64,
                    value: $size,
                ) -> Result<(), ExitRequest> {
                    let guest_address = Address(address_inside_region + self.phys_offset.0);
                    tracing::event!(
                        target: tracing::TraceItem::Memory.as_str(),
                        tracing::Level::TRACE,
                        kind = "write",
                        size = stringify!($size),
                        address = ?guest_address,
                        value = ?tracing::BinaryHex(value),
                    );
                    // Check that we do not exceed region size
                    assert!(
                        address_inside_region as usize + std::mem::size_of::<$size>()
                        <= self.len() as usize
                    );
                    match self.backing {
                        MemoryBacking::Mmap(ref mut map @ MmappedMemory { .. }) => {
                            let destination =
                                // SAFETY: when resolving the guest address to a memory region, we
                                // essentially performed a bounds check so we know this offset is
                                // valid.
                                unsafe { map.as_mut_ptr().add(address_inside_region as usize) };
                            // SAFETY: this is safe since we checked that we do not exceed the
                            // map's size.
                            Ok(unsafe { std::ptr::write_unaligned(destination.cast::<$size>(), value) })
                        }
                        MemoryBacking::Device((_, ref ops)) => {
                            ops.write(
                                address_inside_region,
                                // [ref:TODO] allow for device 128bit IO?
                                u64::try_from(value).unwrap(),
                                match std::mem::size_of::<$size>() {
                                    1 => Width::_8,
                                    2 => Width::_16,
                                    4 => Width::_32,
                                    8 => Width::_64,
                                    16 => Width::_128,
                                    _ => unreachable!(),
                                },
                            )
                        }
                    }
                }
            }
        };
        (read $fn:ident: $size:ty) => {
            impl MemoryRegion {
                pub fn $fn(
                    &self,
                    address_inside_region: u64,
                ) -> Result<$size, ExitRequest> {
                    let guest_address = Address(address_inside_region + self.phys_offset.0);
                    tracing::event!(
                        target: tracing::TraceItem::Memory.as_str(),
                        tracing::Level::TRACE,
                        kind = "read",
                        size = stringify!($size),
                        address = ?guest_address,
                    );
                    // Check that we do not exceed region size
                    assert!(
                        address_inside_region as usize + std::mem::size_of::<$size>()
                        <= self.len() as usize
                    );
                    let value = match self.backing {
                        MemoryBacking::Mmap(ref map @ MmappedMemory {  .. }) => {
                            let destination =
                                // SAFETY: when resolving the guest address to a memory region, we
                                // essentially performed a bounds check so we know this offset is valid.
                                unsafe { map.as_ptr().add(address_inside_region as usize) };
                            // SAFETY: this is safe since we checked that we do not exceed the
                            // map's size.
                            Ok(unsafe { std::ptr::read_unaligned(destination.cast::<$size>()) })
                        }
                        #[allow(clippy::cast_lossless)]
                        MemoryBacking::Device((_, ref ops)) => match ops.read(
                            address_inside_region,
                            match std::mem::size_of::<$size>() {
                                1 => Width::_8,
                                2 => Width::_16,
                                4 => Width::_32,
                                8 => Width::_64,
                                16 => Width::_128,
                                _ => unreachable!(),
                            },
                        ) {
                            Ok(v) => Ok(v as $size),
                            Err(err) => Err(err),
                        }
                    }?;
                    tracing::event!(
                        target: tracing::TraceItem::Memory.as_str(),
                        tracing::Level::TRACE,
                        kind = "read",
                        size = stringify!($size),
                        address = ?Address(address_inside_region + self.phys_offset.0),
                        returning_value = ?tracing::BinaryHex(value),
                    );
                    Ok(value)
                }
            }
        };
    }

    def_op! { write write_8: u8 }
    def_op! { write write_16: u16 }
    def_op! { write write_32: u32 }
    def_op! { write write_64: u64 }
    def_op! { write write_128: u128 }

    def_op! { read read_8: u8 }
    def_op! { read read_16: u16 }
    def_op! { read read_32: u32 }
    def_op! { read read_64: u64 }
    def_op! { read read_128: u128 }
}
