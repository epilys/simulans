// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::collections::BTreeSet;

use crate::memory::Address;

pub struct DebugMonitor {
    /// Whether we have stopped at a breakpoint.
    pub in_breakpoint: bool,
    /// List of breakpoint addresses.
    pub hw_breakpoints: BTreeSet<Address>,
}

impl DebugMonitor {
    pub fn new() -> Self {
        Self {
            in_breakpoint: false,
            hw_breakpoints: BTreeSet::new(),
        }
    }
}

impl Default for DebugMonitor {
    fn default() -> Self {
        Self::new()
    }
}
