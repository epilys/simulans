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

use std::{borrow::Cow, num::NonZero, path::PathBuf};

use clap::Parser;
use simulans::memory::{Address, MemorySize, KERNEL_ADDRESS};

fn maybe_hex(s: &str) -> Result<Address, Cow<'static, str>> {
    const HEX_PREFIX: &str = "0x";
    const HEX_PREFIX_UPPER: &str = "0X";
    const HEX_PREFIX_LEN: usize = HEX_PREFIX.len();

    let result = if s.starts_with(HEX_PREFIX) || s.starts_with(HEX_PREFIX_UPPER) {
        u64::from_str_radix(&s[HEX_PREFIX_LEN..], 16)
    } else {
        s.parse::<u64>()
    };

    result
        .map(Address)
        .map_err(|err| Cow::Owned(err.to_string()))
}

fn memory_size(s: &str) -> Result<MemorySize, Cow<'static, str>> {
    fn err<A>(_: A) -> Cow<'static, str> {
        Cow::Borrowed(
            "Expected decimal or hexadecimal value, with optional prefixes: B (bytes), K/KiB \
             (Kibibytes), M/MiB (Mibibytes) or G/GiB. (A kibibyte is 1024 bytes)",
        )
    }
    fn non_zero_map(
        value: Result<u64, Cow<'static, str>>,
    ) -> Result<MemorySize, Cow<'static, str>> {
        Ok(MemorySize(value?.try_into().map_err(|err| {
            Cow::Owned(format!("Memory size must be non-zero: {err}"))
        })?))
    }
    if let Ok(num) = maybe_hex(s) {
        return non_zero_map(Ok(num.0));
    }

    if let Some(s) = s.strip_suffix("KiB").or_else(|| s.strip_suffix("K")) {
        let mut value = non_zero_map(maybe_hex(s).map(|v| v.0).map_err(err))?;
        value.0 = value.0.checked_mul(MemorySize::KiB).ok_or_else(|| {
            Cow::Owned(format!(
                "{}KiB is too large be represented in 64 bits",
                value.0
            ))
        })?;
        return Ok(value);
    }
    if let Some(s) = s.strip_suffix("MiB").or_else(|| s.strip_suffix("M")) {
        let mut value = non_zero_map(maybe_hex(s).map(|v| v.0).map_err(err))?;
        value.0 = value.0.checked_mul(MemorySize::MiB).ok_or_else(|| {
            Cow::Owned(format!(
                "{}MiB is too large be represented in 64 bits",
                value.0
            ))
        })?;
        return Ok(value);
    }
    if let Some(s) = s.strip_suffix("GiB").or_else(|| s.strip_suffix("G")) {
        let mut value = non_zero_map(maybe_hex(s).map(|v| v.0).map_err(err))?;
        value.0 = value.0.checked_mul(MemorySize::GiB).ok_or_else(|| {
            Cow::Owned(format!(
                "{}GiB is too large be represented in 64 bits",
                value.0
            ))
        })?;
        return Ok(value);
    }
    if let Some(s) = s.strip_suffix("B") {
        return non_zero_map(maybe_hex(s).map(|v| v.0).map_err(err));
    }

    Err(err(()))
}

// SAFETY: Value is non-zero.
const DEFAULT_MEMORY_SIZE: MemorySize =
    MemorySize(NonZero::new(4 * MemorySize::GiB.get()).unwrap());

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
    /// Non-zero hexadecimal or decimal value of the size of available physical
    /// memory to the VM.
    #[arg(long, default_value_t = DEFAULT_MEMORY_SIZE, value_parser=memory_size)]
    pub memory: MemorySize,

    /// Path to binary file containing aarch64 instructions (NOT an ELF file!)
    #[arg(value_name = "BINARY")]
    pub binary: PathBuf,
}

impl Args {
    /// Parse command-line arguments from the process environment.
    pub fn parse() -> Result<Self, String> {
        let retval = <Self as clap::Parser>::parse();
        if retval.start_address.0 >= retval.memory.0.get() {
            return Err(format!(
                "Invalid arguments: Given start address {} is out of range for given memory size \
                 {}.",
                retval.start_address, retval.memory
            ));
        }
        Ok(retval)
    }
}
