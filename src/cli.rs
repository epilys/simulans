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

#![allow(non_upper_case_globals)]

use std::path::PathBuf;

use clap::Parser;
use simulans::KERNEL_ADDRESS;

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct Address(pub u64);

impl std::fmt::Display for Address {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "0x{:x}", self.0)
    }
}

impl std::fmt::Debug for Address {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "0x{:x}", self.0)
    }
}

fn maybe_hex(s: &str) -> Result<Address, String> {
    const HEX_PREFIX: &str = "0x";
    const HEX_PREFIX_UPPER: &str = "0X";
    const HEX_PREFIX_LEN: usize = HEX_PREFIX.len();

    let result = if s.starts_with(HEX_PREFIX) || s.starts_with(HEX_PREFIX_UPPER) {
        u64::from_str_radix(&s[HEX_PREFIX_LEN..], 16)
    } else {
        s.parse::<u64>()
    };

    result.map(Address).map_err(|err| err.to_string())
}

const KiB: u64 = 1024;
const MiB: u64 = KiB * 1024;
const GiB: u64 = MiB * 1024;

#[derive(Copy, Clone)]
#[repr(transparent)]
pub struct MemorySize(pub u64);

impl std::fmt::Display for MemorySize {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let bytes = self.0;
        if bytes == 0 {
            write!(fmt, "0")
        } else if bytes < KiB {
            write!(fmt, "{}bytes", bytes)
        } else if bytes < MiB {
            write!(fmt, "{}KiB", bytes / KiB)
        } else if bytes < GiB {
            write!(fmt, "{}MiB", bytes / MiB)
        } else {
            write!(fmt, "{}GiB", bytes / GiB)
        }
    }
}

impl std::fmt::Debug for MemorySize {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let bytes = self.0;
        if bytes == 0 {
            write!(fmt, "0")
        } else if bytes < KiB {
            write!(fmt, "{}bytes", bytes)
        } else if bytes < MiB {
            write!(fmt, "{}KiB", bytes / KiB)
        } else if bytes < GiB {
            write!(fmt, "{}MiB", bytes / MiB)
        } else {
            write!(fmt, "{}GiB", bytes / GiB)
        }
    }
}

fn memory_size(s: &str) -> Result<MemorySize, String> {
    fn err<A>(_: A) -> String {
        "Expected decimal or hexadecimal value, with optional prefixes: B (bytes), K/KiB \
         (Kibibytes), M/MiB (Mibibytes) or G/GiB. (A kibibyte is 1024 bytes)"
            .to_string()
    }
    if let Ok(num) = maybe_hex(s) {
        return Ok(MemorySize(num.0));
    }

    if let Some(s) = s.strip_suffix("KiB").or_else(|| s.strip_suffix("K")) {
        return Ok(MemorySize(maybe_hex(s).map_err(err)?.0 * KiB));
    }
    if let Some(s) = s.strip_suffix("MiB").or_else(|| s.strip_suffix("M")) {
        return Ok(MemorySize(maybe_hex(s).map_err(err)?.0 * MiB));
    }
    if let Some(s) = s.strip_suffix("GiB").or_else(|| s.strip_suffix("G")) {
        return Ok(MemorySize(maybe_hex(s).map_err(err)?.0 * GiB));
    }
    if let Some(s) = s.strip_suffix("B") {
        return Ok(MemorySize(maybe_hex(s).map_err(err)?.0));
    }

    Err(err(()))
}

/// Armv8-A emulation
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[arg(short, long, default_value_t = 0, action = clap::ArgAction::Count)]
    pub verbose: u8,
    /// Hexadecimal or decimal value of the address to load the binary in to.
    ///
    /// Must be lower than total available memory.
    #[arg(long, default_value_t = Address(KERNEL_ADDRESS as u64), value_parser=maybe_hex)]
    pub start_address: Address,
    /// Hexadecimal or decimal value of the size of available physical memory to
    /// the VM.
    #[arg(long, default_value_t = MemorySize(4 * GiB), value_parser=memory_size)]
    pub memory: MemorySize,
    /// Path to binary file containing aarch64 instructions (NOT an ELF file!)
    #[arg(value_name = "BINARY")]
    pub binary: PathBuf,
}

impl Args {
    /// Parse command-line arguments from the process environment.
    pub fn parse() -> Result<Self, String> {
        let retval = <Self as clap::Parser>::parse();
        if retval.start_address.0 >= retval.memory.0 {
            return Err(format!(
                "Invalid arguments: Given start address {} is out of range for given memory size \
                 {}.",
                retval.start_address, retval.memory
            ));
        }
        Ok(retval)
    }
}
