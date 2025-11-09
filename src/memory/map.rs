// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Virtual machine Memory map

use std::{cmp::Ordering, collections::BTreeMap, ops::Range};

use crate::{
    interval_tree::IntervalTree,
    memory::{Address, MemoryRegion, MemoryRegionDescription, MemorySize},
};

#[derive(Debug)]
/// A builder struct for [`MemoryMap`].
pub struct MemoryMapBuilder {
    interval_tree: IntervalTree<Address>,
    entries: BTreeMap<Address, MemoryRegion>,
    device_registry: DeviceRegistry,
    max_size: MemorySize,
}

#[derive(Debug)]
/// Errors returned by [`MemoryMapBuilder`].
pub enum MemoryMapError {
    /// Adding `region` overflows maximum size of map.
    Overflows {
        /// The memory region value.
        region: MemoryRegion,
        /// The maximum size the map allows.
        max_size: MemorySize,
    },
    /// `region` would overlap with other existing regions.
    Overlaps {
        /// The memory region value.
        region: MemoryRegion,
        /// Which regions overlap.
        overlaps_with: Vec<MemoryRegionDescription>,
    },
}

impl std::fmt::Display for MemoryMapError {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "{self:?}")
    }
}

impl std::error::Error for MemoryMapError {}

impl MemoryMapBuilder {
    #[inline]
    /// Creates a new builder.
    pub fn new() -> Self {
        const MAX_SIZE: MemorySize =
            MemorySize(std::num::NonZero::new(MemorySize::MiB.get() * 1024 * 512).unwrap());
        Self {
            max_size: MAX_SIZE,
            device_registry: DeviceRegistry::new(),
            entries: BTreeMap::default(),
            interval_tree: IntervalTree::default(),
        }
    }

    #[inline]
    pub fn device_registry(&mut self) -> &mut DeviceRegistry {
        &mut self.device_registry
    }

    /// Adds a memory region, takes a mutable reference to `self`.
    pub fn add_region(&mut self, new: MemoryRegion) -> Result<(), MemoryMapError> {
        let range: Range<Address> = Range::from(&new);
        if range.end.0 > self.max_size.0.get() {
            return Err(MemoryMapError::Overflows {
                region: new,
                max_size: self.max_size,
            });
        }
        let overlaps = self.interval_tree.get_interval_overlaps(&range);
        if overlaps.is_empty() {
            self.interval_tree.insert(range);
            self.entries.insert(new.phys_offset, new);
            Ok(())
        } else {
            let overlaps_with = overlaps
                .into_iter()
                .map(|r| {
                    let start = match r.0 {
                        std::collections::Bound::Included(address) => address,
                        other => unreachable!(
                            "got non-Included bound in region overlap search: {:?}",
                            other
                        ),
                    };
                    (&self.entries[&start]).into()
                })
                .collect();
            Err(MemoryMapError::Overlaps {
                region: new,
                overlaps_with,
            })
        }
    }

    /// Adds a memory region and returns a new `Self`.
    pub fn with_region(mut self, new: MemoryRegion) -> Result<Self, MemoryMapError> {
        self.add_region(new)?;
        Ok(self)
    }

    /// Constructs a [`MemoryMap`].
    pub fn build(self) -> MemoryMap {
        let Self {
            entries,
            max_size,
            device_registry: _,
            interval_tree: _,
        } = self;
        let regions: Vec<MemoryRegion> = entries.into_values().collect();
        let index: Vec<((Address, Address), usize)> = regions
            .iter()
            .enumerate()
            .map(|(i, x)| ((x.phys_offset, x.last_addr()), i))
            .collect();
        MemoryMap {
            regions,
            index,
            max_size,
        }
    }
}

impl Default for MemoryMapBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// A flattened memory map of the guest.
///
/// # Example
///
/// ```rust
/// use simulans::memory::*;
///
/// let region = MemoryRegion::new("rom", MemorySize(MemorySize::KiB), Address(0x0)).unwrap();
/// let map = MemoryMap::builder().with_region(region).unwrap().build();
/// assert_eq!(
///     map.max_size().0.get(),
///     MemorySize::MiB.get() * 1024 * 512,
///     "max size"
/// );
/// assert_eq!(map.len(), 1, "region count");
/// let region_ref = map.find_region(Address(0x0)).unwrap();
/// assert_eq!(
///     region_ref.len(),
///     MemorySize::KiB.get() as usize,
///     "memory region length"
/// );
/// assert_eq!(region_ref.start_addr(), Address(0x0), "start address");
/// assert_eq!(
///     region_ref.last_addr(),
///     Address(MemorySize::KiB.get()),
///     "last address"
/// );
/// ```
#[derive(Clone, Debug)]
pub struct MemoryMap {
    regions: Vec<MemoryRegion>,
    index: Vec<((Address, Address), usize)>,
    max_size: MemorySize,
}

impl MemoryMap {
    #[inline]
    /// Return a builder struct.
    pub fn builder() -> MemoryMapBuilder {
        MemoryMapBuilder::new()
    }

    #[inline]
    /// Return the maximum size of this memory map (not necessarily covered
    /// entirely).
    pub const fn max_size(&self) -> MemorySize {
        self.max_size
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    /// Return how many regions this map contains.
    pub const fn len(&self) -> usize {
        self.regions.len()
    }

    /// Return reference of region for given address.
    pub fn find_region(&self, addr: Address) -> Option<&MemoryRegion> {
        self.index
            .binary_search_by(|(probe, _)| {
                if addr < probe.0 {
                    Ordering::Greater
                } else if addr > probe.1 {
                    Ordering::Less
                } else {
                    Ordering::Equal
                }
            })
            .ok()
            .and_then(|i| self.index.get(i))
            .and_then(|(_, i)| self.regions.get(*i))
    }

    /// Return mutable reference of region for given address.
    pub fn find_region_mut(&mut self, addr: Address) -> Option<&mut MemoryRegion> {
        self.index
            .binary_search_by(|(probe, _)| {
                if addr < probe.0 {
                    Ordering::Greater
                } else if addr > probe.1 {
                    Ordering::Less
                } else {
                    Ordering::Equal
                }
            })
            .ok()
            .and_then(|i| self.index.get(i))
            .and_then(|(_, i)| self.regions.get_mut(*i))
    }

    /// Returns an iterator of memory regions.
    pub fn iter(&self) -> impl Iterator<Item = &MemoryRegion> {
        self.regions.iter()
    }
}

#[derive(Copy, Clone, PartialOrd, Ord, Debug, PartialEq, Eq, Hash)]
pub struct DeviceID(u64);

#[derive(Debug)]
pub struct DeviceRegistry {
    counter: u64,
}

impl DeviceRegistry {
    pub fn new() -> Self {
        Self { counter: 0 }
    }

    pub fn register(&mut self) -> DeviceID {
        let id = self.counter;
        self.counter += 1;
        DeviceID(id)
    }
}

impl Default for DeviceRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl vm_memory::guest_memory::GuestMemory for MemoryMap {
    type R = MemoryRegion;

    fn num_regions(&self) -> usize {
        self.len()
    }

    fn find_region(&self, addr: vm_memory::guest_memory::GuestAddress) -> Option<&Self::R> {
        self.find_region(Address(addr.0))
    }

    fn iter(&self) -> impl Iterator<Item = &Self::R> {
        self.iter()
    }
}

impl vm_memory::guest_memory::GuestMemoryRegion for MemoryRegion {
    type B = ();

    fn len(&self) -> vm_memory::guest_memory::GuestUsize {
        self.len() as u64
    }

    fn start_addr(&self) -> vm_memory::guest_memory::GuestAddress {
        vm_memory::guest_memory::GuestAddress(self.start_addr().0)
    }

    fn bitmap(&self) -> &Self::B {
        &()
    }

    fn get_host_address(
        &self,
        addr: vm_memory::guest_memory::MemoryRegionAddress,
    ) -> Result<*mut u8, vm_memory::guest_memory::Error> {
        assert!(addr.0 < self.len() as u64);
        // SAFETY: we checked that addr.0 is within bounds
        Ok(unsafe {
            self.as_mmap()
                .unwrap()
                .lock()
                .unwrap()
                .map
                .as_mut_ptr()
                .add(addr.0 as usize)
        })
    }

    fn get_slice(
        &self,
        offset: vm_memory::guest_memory::MemoryRegionAddress,
        count: usize,
    ) -> Result<
        vm_memory::VolatileSlice<'_, vm_memory::bitmap::BS<'_, Self::B>>,
        vm_memory::guest_memory::Error,
    > {
        assert!(offset.0 + (count as u64) < self.len() as u64);
        let ptr = self.get_host_address(offset)?;
        // SAFETY: we checked that slice offset and count is within bounds
        Ok(unsafe { vm_memory::volatile_memory::VolatileSlice::new(ptr, count) })
    }
}

impl vm_memory::bytes::Bytes<vm_memory::guest_memory::MemoryRegionAddress> for MemoryRegion {
    type E = vm_memory::guest_memory::Error;

    fn write(
        &self,
        buf: &[u8],
        addr: vm_memory::guest_memory::MemoryRegionAddress,
    ) -> Result<usize, Self::E> {
        let addr = addr.0;

        let len = buf
            .len()
            .min((self.len() - addr as usize).saturating_sub(buf.len()));

        for (i, b) in buf.iter().take(len).enumerate() {
            self.write_8(addr + i as u64, *b).unwrap();
        }
        Ok(len)
    }

    fn read(
        &self,
        buf: &mut [u8],
        addr: vm_memory::guest_memory::MemoryRegionAddress,
    ) -> Result<usize, Self::E> {
        let addr = addr.0;

        let len = buf
            .len()
            .min((self.len() - addr as usize).saturating_sub(buf.len()));

        for (i, b) in buf.iter_mut().take(len).enumerate() {
            *b = self.read_8(addr + i as u64).unwrap();
        }
        Ok(len)
    }

    fn write_slice(
        &self,
        _buf: &[u8],
        _addr: vm_memory::guest_memory::MemoryRegionAddress,
    ) -> Result<(), Self::E> {
        todo!()
    }

    fn read_slice(
        &self,
        _buf: &mut [u8],
        _addr: vm_memory::guest_memory::MemoryRegionAddress,
    ) -> Result<(), Self::E> {
        todo!()
    }

    fn read_from<F>(
        &self,
        _: vm_memory::guest_memory::MemoryRegionAddress,
        _: &mut F,
        _: usize,
    ) -> std::result::Result<
        usize,
        <Self as vm_memory::Bytes<vm_memory::guest_memory::MemoryRegionAddress>>::E,
    >
    where
        F: std::io::Read,
    {
        todo!()
    }

    fn read_exact_from<F>(
        &self,
        _: vm_memory::guest_memory::MemoryRegionAddress,
        _: &mut F,
        _: usize,
    ) -> std::result::Result<
        (),
        <Self as vm_memory::Bytes<vm_memory::guest_memory::MemoryRegionAddress>>::E,
    >
    where
        F: std::io::Read,
    {
        todo!()
    }

    fn write_to<F>(
        &self,
        _: vm_memory::guest_memory::MemoryRegionAddress,
        _: &mut F,
        _: usize,
    ) -> std::result::Result<
        usize,
        <Self as vm_memory::Bytes<vm_memory::guest_memory::MemoryRegionAddress>>::E,
    >
    where
        F: std::io::Write,
    {
        todo!()
    }

    fn write_all_to<F>(
        &self,
        _: vm_memory::guest_memory::MemoryRegionAddress,
        _: &mut F,
        _: usize,
    ) -> std::result::Result<
        (),
        <Self as vm_memory::Bytes<vm_memory::guest_memory::MemoryRegionAddress>>::E,
    >
    where
        F: std::io::Write,
    {
        todo!()
    }

    fn store<T: vm_memory::bytes::AtomicAccess>(
        &self,
        val: T,
        addr: vm_memory::guest_memory::MemoryRegionAddress,
        // [ref:atomics]
        _order: core::sync::atomic::Ordering,
    ) -> Result<(), Self::E> {
        for (i, b) in val.as_slice().iter().enumerate() {
            self.write_8(addr.0 + i as u64, *b).unwrap();
        }
        Ok(())
    }

    fn load<T: vm_memory::bytes::AtomicAccess>(
        &self,
        addr: vm_memory::guest_memory::MemoryRegionAddress,
        // [ref:atomics]
        _order: core::sync::atomic::Ordering,
    ) -> Result<T, Self::E> {
        // SAFETY: T is also ByteValued so it is PDT
        let val: T = unsafe { std::mem::zeroed() };
        let bytes_no = val.as_slice().len();
        let mut bytes = vec![];
        for i in 0..bytes_no {
            bytes.push(self.read_8(addr.0 + i as u64).unwrap());
        }
        Ok(*T::from_slice(&bytes).unwrap())
    }
}
