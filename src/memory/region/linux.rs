// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

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
