// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

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
    pub fn new_region(_name: &str, size: MemorySize) -> Result<Self, Errno> {
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
        Ok(Self {
            size: size_u.into(),
            map,
            read_only: false,
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
