// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Memory region types

#![allow(clippy::len_without_is_empty)]

use std::{cmp::Ordering, ops::Range, path::PathBuf};

#[cfg(target_os = "linux")]
pub use linux::MmappedMemory;
#[cfg(target_os = "macos")]
pub use macos::MmappedMemory;
use nix::errno::Errno;

use crate::memory::{Address, MemorySize, Width};

#[cfg(target_os = "linux")]
mod linux {
    use std::{ffi::CString, ops::Deref, os::fd::OwnedFd, path::PathBuf};

    use nix::{
        errno::Errno,
        sys::{memfd, mman::ProtFlags},
    };

    use crate::memory::{Address, MemorySize};

    /// A linux mmapped region.
    pub struct MmappedMemory {
        /// User-friendly name.
        pub name: String,
        /// Owned file descriptor.
        pub fd: OwnedFd,
        /// Mapping.
        pub map: memmap2::MmapMut,
        /// Read-only status.
        pub read_only: bool,
        /// Filesystem path.
        pub fs_path: Option<PathBuf>,
    }

    impl std::fmt::Debug for MmappedMemory {
        fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
            fmt.debug_struct("MmappedMemory")
                .field("name", &self.name)
                .field("fd", &self.fd)
                .field("read_only", &self.read_only)
                .field("fs_path", &self.fs_path)
                .finish_non_exhaustive()
        }
    }

    impl PartialEq for MmappedMemory {
        fn eq(&self, other: &Self) -> bool {
            use std::os::fd::AsRawFd;

            self.fd.as_raw_fd() == other.fd.as_raw_fd()
        }
    }

    impl Eq for MmappedMemory {}

    impl MmappedMemory {
        /// Returns new region from file descriptor.
        fn new_from_fd(
            name: &str,
            fd: OwnedFd,
            fs_path: Option<PathBuf>,
            size: MemorySize,
            phys_offset: Address,
        ) -> Result<super::MemoryRegion, Errno> {
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
            // Don't include VM memory in dumped core files.
            _ = map.advise(memmap2::Advice::DontDump);
            let u_size: usize = size.get().try_into().map_err(|_| Errno::ERANGE)?;
            debug_assert_eq!(map.len(), u_size);
            Ok(super::MemoryRegion {
                phys_offset,
                size,
                backing: super::MemoryBacking::Mmap(Self {
                    name: name.to_string(),
                    fd,
                    map,
                    fs_path,
                    read_only: false,
                }),
            })
        }

        /// Creates a new memfd-backed mmapped memory region.
        pub fn new_region(
            name: &str,
            size: MemorySize,
            phys_offset: Address,
        ) -> Result<super::MemoryRegion, Errno> {
            let fd = memfd::memfd_create(
                CString::new(name).unwrap().as_c_str(),
                memfd::MFdFlags::MFD_CLOEXEC,
            )?;
            Self::new_from_fd(name, fd, None, size, phys_offset)
        }

        /// Creates a new file-backed mmapped memory region.
        pub fn new_file_region(
            name: &str,
            path: PathBuf,
            size: MemorySize,
            phys_offset: Address,
        ) -> Result<super::MemoryRegion, Errno> {
            let file = match std::fs::OpenOptions::new()
                .read(true)
                .write(true)
                .create_new(true)
                .open(&path)
            {
                Ok(f) => f,
                Err(err) => {
                    tracing::error!("Could not open {}: {err}", path.display());
                    return Err(Errno::EINVAL);
                }
            };
            let fd = file.into();
            Self::new_from_fd(name, fd, Some(path), size, phys_offset)
        }

        #[inline]
        // False positive; memmap2::MapMut::as_ptr() is not const.
        #[allow(clippy::missing_const_for_fn)]
        /// Return mapping as byte pointer.
        pub fn as_ptr(&self) -> *const u8 {
            self.map.as_ptr().cast()
        }

        #[inline]
        // False positive; memmap2::MapMut::as_mut_ptr() is not const.
        #[allow(clippy::missing_const_for_fn)]
        /// Return mapping as mutable byte pointer.
        pub fn as_mut_ptr(&mut self) -> *mut u8 {
            self.map.as_mut_ptr()
        }
    }

    impl Deref for MmappedMemory {
        type Target = [u8];

        #[inline]
        fn deref(&self) -> &[u8] {
            self.map.deref()
        }
    }

    impl std::ops::DerefMut for MmappedMemory {
        #[inline]
        fn deref_mut(&mut self) -> &mut [u8] {
            self.map.deref_mut()
        }
    }

    impl AsRef<[u8]> for MmappedMemory {
        #[inline]
        fn as_ref(&self) -> &[u8] {
            self.deref()
        }
    }
}

#[cfg(target_os = "macos")]
mod macos {
    use std::{ffi::c_void, ops::Deref, ptr::NonNull};

    use nix::{errno::Errno, sys::mman::ProtFlags};

    use crate::memory::{Address, MemorySize};

    pub struct MmappedMemory {
        map: NonNull<c_void>,
        pub size: usize,
        pub read_only: bool,
    }

    // SAFETY: no one else has access to `map` field
    unsafe impl Send for MmappedMemory {}

    impl Drop for MmappedMemory {
        fn drop(&mut self) {
            // SAFETY: `self.map` is a valid mmapped ptr of this size.
            _ = unsafe { nix::sys::mman::munmap(self.map, self.size) };
        }
    }

    impl std::fmt::Debug for MmappedMemory {
        fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
            fmt.debug_struct("MmappedMemory")
                .field("ptr", &self.map)
                .field("size", &self.size)
                .field("read_only", &self.read_only)
                .finish_non_exhaustive()
        }
    }

    impl PartialEq for MmappedMemory {
        fn eq(&self, other: &Self) -> bool {
            self.map.as_ptr() == other.map.as_ptr()
        }
    }

    impl Eq for MmappedMemory {}

    impl MmappedMemory {
        pub fn new_region(
            _name: &str,
            size: MemorySize,
            phys_offset: Address,
        ) -> Result<super::MemoryRegion, Errno> {
            {
                extern "C" {
                    fn pthread_jit_write_protect_np(_: bool);
                }
                // SAFETY: this is safe to call.
                unsafe { pthread_jit_write_protect_np(false) };
            }
            let size_u: std::num::NonZero<usize> = size.0.try_into().unwrap();
            // SAFETY: This is safe to call.
            let map = unsafe {
                nix::sys::mman::mmap_anonymous(
                    None,
                    size_u,
                    ProtFlags::PROT_READ | ProtFlags::PROT_WRITE | ProtFlags::PROT_EXEC,
                    nix::sys::mman::MapFlags::MAP_PRIVATE | nix::sys::mman::MapFlags::MAP_JIT,
                )
                .unwrap()
            };
            Ok(super::MemoryRegion {
                phys_offset,
                size,
                backing: super::MemoryBacking::Mmap(Self {
                    size: size_u.into(),
                    map,
                    read_only: false,
                }),
            })
        }

        #[inline]
        #[allow(clippy::missing_const_for_fn)]
        pub fn as_ptr(&self) -> *const u8 {
            self.map.as_ptr().cast()
        }

        #[inline]
        #[allow(clippy::missing_const_for_fn)]
        pub fn as_mut_ptr(&mut self) -> *mut u8 {
            self.map.as_ptr().cast()
        }
    }

    impl std::ops::Deref for MmappedMemory {
        type Target = [u8];

        #[inline]
        fn deref(&self) -> &[u8] {
            // SAFETY: `self.map` is an mmapped region of this size.
            unsafe { std::slice::from_raw_parts(self.map.as_ptr().cast(), self.size) }
        }
    }

    impl std::ops::DerefMut for MmappedMemory {
        #[inline]
        fn deref_mut(&mut self) -> &mut [u8] {
            // SAFETY: `self.map` is an mmapped region of this size.
            unsafe { std::slice::from_raw_parts_mut(self.map.as_ptr().cast(), self.size) }
        }
    }

    impl AsRef<[u8]> for MmappedMemory {
        #[inline]
        fn as_ref(&self) -> &[u8] {
            self.deref()
        }
    }
}

/// Trait for device memory operations.
pub trait DeviceMemoryOps: std::fmt::Debug + Send + Sync {
    /// Returns unique device ID.
    fn id(&self) -> u64;
    /// Performs a read.
    fn read(&self, address_inside_region: u64, width: Width) -> u64;
    /// Performs a write.
    fn write(&self, address_inside_region: u64, value: u64, width: Width);
}

impl PartialEq for &dyn DeviceMemoryOps {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for &dyn DeviceMemoryOps {}

#[derive(Debug)]
/// Kind of memory backing.
pub enum MemoryBacking {
    /// A mmapped region.
    Mmap(MmappedMemory),
    /// Device memory.
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
        MmappedMemory::new_region(name, size, phys_offset)
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
        MmappedMemory::new_file_region(name, path, size, phys_offset)
    }

    /// Creates a new I/O memory region.
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

    use std::mem::MaybeUninit;

    use super::*;
    use crate::tracing;

    macro_rules! def_op {
        (write $fn:ident: $size:ty) => {
            /// Helper memory write struct called from JIT code.
            pub extern "C" fn $fn(
                mem_region: &mut MemoryRegion,
                address_inside_region: u64,
                value: $size,
            ) {
                tracing::event!(
                    target: tracing::TraceItem::Memory.as_str(),
                    tracing::Level::TRACE,
                    kind = "write",
                    size = stringify!($size),
                    address = ?Address(address_inside_region),
                    value = ?tracing::BinaryHex(value),
                );
                match mem_region.backing {
                    MemoryBacking::Mmap(ref mut map @ MmappedMemory { .. }) => {
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
                        );
                    }
                }
            }
        };
        (read $fn:ident: $size:ty) => {
            /// Helper memory read struct called from JIT code.
            pub extern "C" fn $fn(
                mem_region: &MemoryRegion,
                address_inside_region: u64,
                ret: &mut MaybeUninit<$size>,
            ) {
                tracing::event!(
                    target: tracing::TraceItem::Memory.as_str(),
                    tracing::Level::TRACE,
                    kind = "read",
                    size = stringify!($size),
                    address = ?Address(address_inside_region),
                    inside_offset = ?Address(address_inside_region),
                );
                let value = match mem_region.backing {
                    MemoryBacking::Mmap(ref map @ MmappedMemory {  .. }) => {
                        let destination =
                        // SAFETY: when resolving the guest address to a memory region, we
                        // essentially performed a bounds check so we know this offset is valid.
                            unsafe { map.as_ptr().add(address_inside_region as usize) };
                        // SAFETY: this is safe as long as $size width does not exceed the map's
                        // size. We don't check for this, so FIXME
                        unsafe { std::ptr::read_unaligned(destination.cast::<$size>()) }
                    }
                    #[allow(clippy::cast_lossless)]
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
                };
                tracing::event!(
                    target: tracing::TraceItem::Memory.as_str(),
                    tracing::Level::TRACE,
                    kind = "read",
                    size = stringify!($size),
                    address = ?Address(address_inside_region),
                    inside_offset = ?Address(address_inside_region),
                    returning_value = ?tracing::BinaryHex(value),
                );
                ret.write(value);
            }
        };
    }

    def_op! { write memory_region_write_8: u8 }
    def_op! { write memory_region_write_16: u16 }
    def_op! { write memory_region_write_32: u32 }
    def_op! { write memory_region_write_64: u64 }
    def_op! { write memory_region_write_128: u128 }

    def_op! { read memory_region_read_8: u8 }
    def_op! { read memory_region_read_16: u16 }
    def_op! { read memory_region_read_32: u32 }
    def_op! { read memory_region_read_64: u64 }
    def_op! { read memory_region_read_128: u128 }
}
