// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::{borrow::Cow, num::NonZero, path::PathBuf};

use clap::Parser;
use simulans::{
    cpu_state::ExceptionLevel,
    memory::{Address, MemorySize, KERNEL_ADDRESS, PHYS_MEM_START},
    tracing::TraceItem,
};

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

fn elx(s: &str) -> Result<u8, Box<dyn std::error::Error + Send + Sync>> {
    let result = s.parse::<u8>()?;
    match result {
        1..=3 => Ok(result),
        _ => Err("Value must be in 1, 2, 3".into()),
    }
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
    entry_point_address: Address,

    /// Hexadecimal or decimal value of the address where DRAM starts.
    ///
    /// Must be lower than total available memory.
    #[arg(long, default_value_t = Address(PHYS_MEM_START as u64), value_parser=maybe_hex)]
    dram_start_address: Address,

    /// Non-zero hexadecimal or decimal value of the size of available physical
    /// memory to the VM.
    #[arg(long, default_value_t = DEFAULT_MEMORY_SIZE, value_parser=memory_size)]
    memory: MemorySize,

    /// Map RAM to file (must not already exist) instead of anonymous memory
    /// mapping.
    #[arg(long, default_value = None, value_name = "FILE")]
    pub memory_backend: Option<PathBuf>,

    /// Path to binary file containing aarch64 instructions (NOT an ELF file!)
    #[arg(value_name = "BINARY")]
    pub binary: PathBuf,

    /// Whether to generate an FDT and pass it as `x0` or not.
    #[arg(short, long, default_value_t = true)]
    pub generate_fdt: bool,

    /// Hexadecimal or decimal value of the address to load the FDT to.
    #[arg(long, default_value = None, value_parser=maybe_hex)]
    pub fdt_address: Option<Address>,

    /// Maximum exception level.
    #[arg(long, default_value_t = 1, value_parser=elx)]
    max_el: u8,

    /// Pass boot arguments to kernel (requires Devicetree generation)
    #[arg(long)]
    pub bootargs: Option<String>,

    /// Dump generated device tree blob to file.
    #[arg(long)]
    pub dump_dtb: Option<PathBuf>,

    /// Start a GDB stub instead at given Unix domain socket path.
    #[arg(long)]
    pub gdb_stub_path: Option<PathBuf>,

    #[command(flatten)]
    pub trace: Trace,
}

#[derive(Parser, Debug)]
pub struct Trace {
    #[command(flatten)]
    pub destination: Option<TraceDestination>,

    #[allow(clippy::struct_field_names)]
    #[arg(long, value_name = "ITEM", value_delimiter = ',')]
    /// By default named trace items are not logged and must be enabled.
    pub trace_items: Vec<TraceItem>,

    #[arg(long, value_name = "WHEN")]
    /// Color output.
    pub color: Option<clap::ColorChoice>,
}

#[derive(Parser, Debug)]
#[group(required = false, multiple = false)]
pub struct TraceDestination {
    /// Output logs to standard output.
    #[arg(long = "trace")]
    pub stdout: bool,

    #[arg(long = "trace-stderr")]
    /// Output logs to standard error.
    pub stderr: bool,

    #[arg(long = "trace-file", value_name = "LOG_FILE")]
    /// Output logs to specified file (will be created).
    pub file: Option<PathBuf>,
}

impl Args {
    /// Parse command-line arguments from the process environment.
    pub fn parse() -> Result<Self, String> {
        let retval = <Self as clap::Parser>::parse();
        if retval.entry_point_address.0 >= (retval.dram_start_address.0 + retval.memory.0.get()) {
            return Err(format!(
                "Invalid arguments: Given entry point address {} is out of range for given memory \
                 size {}.",
                retval.entry_point_address, retval.memory
            ));
        }
        if retval.entry_point_address.0 < retval.dram_start_address.0 {
            return Err(format!(
                "Invalid arguments: Given entry point address {} is below start of DRAM address \
                 {}.",
                retval.entry_point_address, retval.dram_start_address
            ));
        }
        Ok(retval)
    }

    /// Hexadecimal or decimal value of the address to load the binary in to.
    ///
    /// Must be lower than total available memory.
    pub const fn entry_point_address(&self) -> Address {
        self.entry_point_address
    }

    /// Hexadecimal or decimal value of the address where DRAM starts.
    ///
    /// Must be lower than total available memory.
    pub const fn dram_start_address(&self) -> Address {
        self.dram_start_address
    }

    /// Non-zero hexadecimal or decimal value of the size of available physical
    /// memory to the VM.
    pub const fn memory(&self) -> MemorySize {
        self.memory
    }

    /// Initial/maximum Exception level.
    pub const fn el(&self) -> ExceptionLevel {
        match self.max_el {
            1 => ExceptionLevel::EL1,
            2 => ExceptionLevel::EL2,
            3 => ExceptionLevel::EL3,
            _ => panic!(),
        }
    }
}
