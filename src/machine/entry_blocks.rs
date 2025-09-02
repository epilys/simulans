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

#[must_use]
pub struct EntryBlock {
    pub start: u64,
    pub end: u64,
    pub entry: Entry,
    pub ctx: cranelift_jit::JITModule,
}

impl EntryBlock {
    fn free(self) {
        let module = self.ctx;
        // SAFETY: After we drop the block, nobody should be able to call self.entry.
        unsafe { module.free_memory() };
    }
}

pub struct EntryBlocks {
    pub entries: BTreeMap<u64, EntryBlock>,
}

impl Drop for EntryBlocks {
    fn drop(&mut self) {
        self.clear();
    }
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
    pub fn get(&self, pc: &u64) -> Option<&EntryBlock> {
        self.entries.get(pc)
    }

    #[inline]
    pub fn insert(&mut self, block: EntryBlock) {
        let start = block.start;
        self.entries.insert(start, block);
    }

    #[inline]
    pub fn clear(&mut self) {
        while let Some((_, b)) = self.entries.pop_first() {
            b.free();
        }
    }

    #[inline]
    pub fn invalidate(&mut self, pc: u64) {
        let invalidated_keys = self
            .entries
            .range(pc..=pc)
            .map(|(k, _)| *k)
            .collect::<Vec<_>>();
        if !invalidated_keys.is_empty() {
            tracing::trace!(
                "Invalidating {} entry block{} at address 0x{:x}",
                invalidated_keys.len(),
                if invalidated_keys.len() == 1 { "" } else { "s" },
                pc
            );
            for k in invalidated_keys {
                if let Some(b) = self.entries.remove(&k) {
                    b.free();
                }
            }
        }
    }

    #[inline]
    pub fn invalidate_range(&mut self, range: RangeInclusive<u64>) {
        let invalidated_keys = self
            .entries
            .range(range.clone())
            .map(|(k, _)| *k)
            .collect::<Vec<_>>();
        if !invalidated_keys.is_empty() {
            tracing::trace!(
                "Invalidating {} entry block{} at address range 0x{:x}-0x{:x}",
                invalidated_keys.len(),
                if invalidated_keys.len() == 1 { "" } else { "s" },
                range.start(),
                range.end()
            );
            for k in invalidated_keys {
                if let Some(b) = self.entries.remove(&k) {
                    b.free();
                }
            }
        }
    }
}
