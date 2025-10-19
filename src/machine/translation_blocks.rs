// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Translation block cache

use std::cmp::Ordering;

use crate::jit::Entry;

#[must_use]
/// A translated block of instructions.
///
/// Before dropped, [`TranslationBlock::free`] must be called.
pub struct TranslationBlock {
    /// First instruction address (physical).
    pub start: u64,
    /// Final physical instruction address (inclusive).
    pub end: u64,
    pub virtual_addr: u64,
    /// The translated function entry.
    pub entry: Entry,
    /// Compiled for single step execution.
    pub single_step: bool,
    /// The JIT context, used to free the memory.
    pub ctx: cranelift_jit::JITModule,
}

impl std::fmt::Debug for TranslationBlock {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("TranslationBlock")
            .field(
                "physical_range",
                &format!("{:#x}-{:#x}", self.start, self.end),
            )
            .field(
                "virtual_range",
                &format!(
                    "{:#x}-{:#x}",
                    self.virtual_addr,
                    (self.virtual_addr + (self.end - self.start))
                ),
            )
            .finish_non_exhaustive()
    }
}

impl TranslationBlock {
    /// Free JIT memory for this block.
    pub fn free(self) {
        let module = self.ctx;
        // SAFETY: After we drop the block, nobody should be able to call self.entry.
        unsafe { module.free_memory() };
    }
}

/// Helper container struct for translated blocks.
pub struct TranslationBlocks {
    /// A map from program counter to block.
    pub entries: Vec<(u64, TranslationBlock)>,
}

impl Drop for TranslationBlocks {
    /// Frees block memory.
    fn drop(&mut self) {
        self.clear();
    }
}

impl Default for TranslationBlocks {
    fn default() -> Self {
        Self::new()
    }
}

impl TranslationBlocks {
    #[inline]
    /// Create an empty container.
    pub fn new() -> Self {
        Self { entries: vec![] }
    }

    #[inline]
    /// Get a translated block for this program counter.
    pub fn get(&mut self, physical_pc: &u64, virtual_pc: &u64) -> Option<&TranslationBlock> {
        let idx = self
            .entries
            .binary_search_by(|probe| {
                (&probe.0, &probe.1.virtual_addr).cmp(&(physical_pc, virtual_pc))
            })
            .ok()?;
        Some(&self.entries[idx].1)
    }

    #[inline]
    /// Insert translated block.
    pub fn insert(&mut self, block: TranslationBlock) {
        let start = block.start;
        match self.entries.binary_search_by(|probe| {
            (probe.0, probe.1.virtual_addr).cmp(&(start, block.virtual_addr))
        }) {
            Ok(idx) => {
                let (_, tb) = std::mem::replace(&mut self.entries[idx], (start, block));
                tb.free();
            }
            Err(idx) => {
                self.entries.insert(idx, (start, block));
            }
        }
    }

    #[inline]
    /// Pop and free all blocks.
    pub fn clear(&mut self) {
        for (_, b) in self.entries.drain(..) {
            b.free();
        }
    }

    #[inline]
    /// Invalidate all translated blocks that touch this program counter.
    pub fn invalidate(&mut self, pc: u64) {
        while let Ok(idx) = self.entries.binary_search_by(|(_, probe)| {
            if pc < probe.start {
                Ordering::Greater
            } else if pc > probe.end {
                Ordering::Less
            } else {
                Ordering::Equal
            }
        }) {
            let (_, tb) = self.entries.remove(idx);
            tb.free();
        }
    }
}
