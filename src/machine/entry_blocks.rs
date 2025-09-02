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

//! Translated entry block cache

use std::{collections::BTreeMap, ops::RangeInclusive};

use crate::jit::Entry;

#[repr(C)]
pub struct EntryBlocks {
    pub entries: BTreeMap<u64, (u64, Entry)>,
}

impl Default for EntryBlocks {
    fn default() -> Self {
        Self::new()
    }
}

impl EntryBlocks {
    #[inline]
    pub fn new() -> Self {
        Self {
            entries: BTreeMap::default(),
        }
    }

    #[inline]
    pub fn get(&self, pc: &u64) -> Option<&(u64, Entry)> {
        self.entries.get(pc)
    }

    #[inline]
    pub fn insert(&mut self, pc_range: RangeInclusive<u64>, entry: Entry) {
        self.entries
            .insert(*pc_range.start(), (*pc_range.end(), entry));
    }

    #[inline]
    pub fn clear(&mut self) {
        self.entries.clear()
    }

    #[inline]
    pub fn invalidate(&mut self, pc: u64) {
        let invalidated_keys = self
            .entries
            .range(pc..=pc)
            .map(|(k, _)| *k)
            .collect::<Vec<_>>();
        tracing::trace!(
            "Invalidating {} entry block{} at address 0x{:x}",
            invalidated_keys.len(),
            if invalidated_keys.len() == 1 { "" } else { "s" },
            pc
        );
        for k in invalidated_keys {
            self.entries.remove(&k);
        }
    }

    #[inline]
    pub fn invalidate_range(&mut self, range: RangeInclusive<u64>) {
        let invalidated_keys = self
            .entries
            .range(range.clone())
            .map(|(k, _)| *k)
            .collect::<Vec<_>>();
        tracing::trace!(
            "Invalidating {} entry block{} at address range 0x{:x}-0x{:x}",
            invalidated_keys.len(),
            if invalidated_keys.len() == 1 { "" } else { "s" },
            range.start(),
            range.end()
        );
        for k in invalidated_keys {
            self.entries.remove(&k);
        }
    }
}
