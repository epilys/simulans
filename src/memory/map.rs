// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Virtual machine Memory map

use std::{collections::BTreeMap, ops::Range};

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
        MemoryMap {
            regions: entries.into_values().collect(),
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
#[derive(Debug)]
pub struct MemoryMap {
    regions: Vec<MemoryRegion>,
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
        let index = match self.regions.binary_search_by_key(&addr, |x| x.phys_offset) {
            Ok(x) => Some(x),
            // Within the closest region with starting address < addr
            Err(x) if (x > 0 && addr.0 <= self.regions[x - 1].last_addr().0) => Some(x - 1),
            _ => None,
        };
        index.and_then(|x| self.regions.get(x))
    }

    /// Return mutable reference of region for given address.
    pub fn find_region_mut(&mut self, addr: Address) -> Option<&mut MemoryRegion> {
        let index = match self.regions.binary_search_by_key(&addr, |x| x.phys_offset) {
            Ok(x) => Some(x),
            // Within the closest region with starting address < addr
            Err(x) if (x > 0 && addr.0 <= self.regions[x - 1].last_addr().0) => Some(x - 1),
            _ => None,
        };
        index.and_then(|x| self.regions.get_mut(x))
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
