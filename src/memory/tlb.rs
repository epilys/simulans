// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Translation lookaside buffer

use std::cell::RefCell;

use uluru::LRUCache;

use crate::memory::mmu::{Permissions, TTWState};

#[derive(Copy, Clone, Debug)]
pub struct Page {
    pub paddress: u64,
    pub permissions: Permissions,
    pub walkstate: TTWState,
}

struct TLBInner {
    global_map: Vec<(u64, Page)>,
    global_lru: LRUCache<u64, 1024>,
    map: Vec<((u16, u64), Page)>,
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
                global_map: Vec::with_capacity(1024),
                global_lru: LRUCache::default(),
                map: Vec::with_capacity(2048),
                lru: LRUCache::default(),
            }
            .into(),
        }
    }

    /// Get a page for an address
    pub fn get(&self, key: &(u16, u64)) -> Option<Page> {
        let mut inner = self.inner.borrow_mut();
        if let Ok(idx) = inner
            .global_map
            .binary_search_by(|probe| probe.0.cmp(&key.1))
        {
            let page = inner.global_map[idx].1;
            inner.global_lru.touch(|a| a == &key.1);
            return Some(page);
        }
        if let Ok(idx) = inner.map.binary_search_by(|probe| probe.0.cmp(key)) {
            let page = inner.map[idx].1;
            inner.lru.touch(|a| a == key);
            return Some(page);
        }
        None
    }

    /// Insert address and page pair
    pub fn insert(
        &self,
        is_global: bool,
        vaddress: u64,
        paddress: u64,
        permissions: Permissions,
        walkstate: TTWState,
    ) {
        let mut inner = self.inner.borrow_mut();
        if is_global {
            if let Some(to_remove) = inner.global_lru.insert(vaddress) {
                let idx = inner
                    .global_map
                    .binary_search_by(|probe| probe.0.cmp(&to_remove))
                    .unwrap();
                inner.global_map.remove(idx);
            }
            let idx = inner
                .global_map
                .partition_point(|probe| probe.0 <= vaddress);
            inner.global_map.insert(
                idx,
                (
                    vaddress,
                    Page {
                        paddress,
                        permissions,
                        walkstate,
                    },
                ),
            );
        } else {
            let key = (walkstate.asid, vaddress);
            if let Some(to_remove) = inner.lru.insert(key) {
                let idx = inner
                    .map
                    .binary_search_by(|probe| probe.0.cmp(&to_remove))
                    .unwrap();
                inner.map.remove(idx);
            }
            let idx = inner.map.partition_point(|probe| probe.0 <= key);
            inner.map.insert(
                idx,
                (
                    key,
                    Page {
                        paddress,
                        permissions,
                        walkstate,
                    },
                ),
            );
        }
    }

    /// Clear buffer
    pub fn clear(&self) {
        let mut inner = self.inner.borrow_mut();
        inner.map.clear();
        inner.lru.clear();
        inner.global_map.clear();
        inner.global_lru.clear();
    }
}

impl Default for TLB {
    fn default() -> Self {
        Self::new()
    }
}
