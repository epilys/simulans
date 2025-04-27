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

use std::{collections::BTreeMap, ops::Range};

use crate::{
    interval_tree::IntervalTree,
    memory::{Address, MemoryRegion, MemoryRegionDescription, MemorySize},
};

#[derive(Debug)]
pub struct MemoryMapBuilder {
    interval_tree: IntervalTree<Address>,
    entries: BTreeMap<Address, MemoryRegion>,
    max_size: MemorySize,
}

#[derive(Debug)]
pub enum MemoryMapError {
    Overflows {
        region: MemoryRegion,
        range_end: Address,
        max_size: MemorySize,
    },
    Overlaps {
        region: MemoryRegion,
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
    pub fn new(max_size: MemorySize) -> Self {
        Self {
            max_size,
            entries: BTreeMap::default(),
            interval_tree: IntervalTree::default(),
        }
    }

    pub fn add_region(&mut self, new: MemoryRegion) -> Result<(), MemoryMapError> {
        let range: Range<Address> = Range::from(&new);
        if range.end.0 > self.max_size.0.get() {
            return Err(MemoryMapError::Overflows {
                region: new,
                range_end: range.end,
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

    pub fn with_region(mut self, new: MemoryRegion) -> Result<Self, MemoryMapError> {
        self.add_region(new)?;
        Ok(self)
    }

    pub fn build(self) -> MemoryMap {
        let Self {
            entries,
            max_size,
            interval_tree: _,
        } = self;
        MemoryMap {
            regions: entries.into_values().collect(),
            max_size,
        }
    }
}

/// A flattened memory map of the guest.
///
/// # Example
///
/// ```rust
/// use simulans::memory::*;
///
/// let overflows_err = MemoryMap::builder(MemorySize(0x100.try_into().unwrap()))
///     .with_region(MemoryRegion::new("rom", MemorySize(MemorySize::KiB), Address(0x0)).unwrap())
///     .unwrap_err();
/// let region = match overflows_err {
///     MemoryMapError::Overflows { region, .. } => region,
///     other => panic!("Expected overflow error, got: {:?}", other),
/// };
/// let map = MemoryMap::builder(MemorySize((MemorySize::KiB.get() * 2).try_into().unwrap()))
///     .with_region(region)
///     .unwrap()
///     .build();
/// assert_eq!(
///     map.max_size().0.get(),
///     MemorySize::KiB.get() * 2,
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
    pub fn builder(max_size: MemorySize) -> MemoryMapBuilder {
        MemoryMapBuilder::new(max_size)
    }

    #[inline]
    pub const fn max_size(&self) -> MemorySize {
        self.max_size
    }

    #[inline]
    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.regions.len()
    }

    pub fn find_region(&self, addr: Address) -> Option<&MemoryRegion> {
        let index = match self.regions.binary_search_by_key(&addr, |x| x.phys_offset) {
            Ok(x) => Some(x),
            // Within the closest region with starting address < addr
            Err(x) if (x > 0 && addr.0 <= self.regions[x - 1].last_addr().0) => Some(x - 1),
            _ => None,
        };
        index.and_then(|x| self.regions.get(x))
    }

    pub fn find_region_mut(&mut self, addr: Address) -> Option<&mut MemoryRegion> {
        let index = match self.regions.binary_search_by_key(&addr, |x| x.phys_offset) {
            Ok(x) => Some(x),
            // Within the closest region with starting address < addr
            Err(x) if (x > 0 && addr.0 <= self.regions[x - 1].last_addr().0) => Some(x - 1),
            _ => None,
        };
        index.and_then(|x| self.regions.get_mut(x))
    }

    pub fn iter(&self) -> impl Iterator<Item = &MemoryRegion> {
        self.regions.iter()
    }
}
