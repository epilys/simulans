// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Translation lookaside buffer

use std::{cell::RefCell, collections::BTreeMap};

use uluru::LRUCache;

struct TLBInner {
    map: BTreeMap<(u16, u64), u64>,
    lru: LRUCache<(u16, u64), 2048>,
}

/// Translation lookaside buffer
pub struct TLB {
    inner: RefCell<TLBInner>,
}

impl TLB {
    /// Create an empty buffer
    pub fn new() -> Self {
        Self {
            inner: TLBInner {
                map: BTreeMap::new(),
                lru: LRUCache::default(),
            }
            .into(),
        }
    }

    /// Get a page for an address
    pub fn get(&self, addr: &(u16, u64)) -> Option<u64> {
        let mut inner = self.inner.borrow_mut();
        if let Some(page) = inner.map.get(addr).copied() {
            inner.lru.touch(|a| a == addr);
            return Some(page);
        }
        None
    }

    /// Insert address and page pair
    pub fn insert(&self, addr: (u16, u64), page: u64) {
        let mut inner = self.inner.borrow_mut();
        if let Some(to_remove) = inner.lru.insert(addr) {
            inner.map.remove(&to_remove);
        }
        inner.map.insert(addr, page);
    }

    /// Clear buffer
    pub fn clear(&self) {
        let mut inner = self.inner.borrow_mut();
        inner.map.clear();
        inner.lru.clear();
    }
}

impl Default for TLB {
    fn default() -> Self {
        Self::new()
    }
}
