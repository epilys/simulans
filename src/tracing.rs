// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

#![deny(missing_docs)]

//! # Tracing support
//!
//! ## Trace items
//!
//! Various trace items are offerred which are disabled by default and must be
//! individually enabled.
//!
//! See [`TraceItem`] variants.

use std::{
    cell::Cell,
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

pub use ::tracing::{error, event, event_enabled, info, trace, warn, Level};
pub use tracing_subscriber::filter::LevelFilter;
use tracing_subscriber::{prelude::*, reload, Layer};

mod helpers {
    /// Helper method to print register state on block entry/exit for trace item
    /// [`BlockEntry`](crate::tracing::TraceItem::BlockEntry)
    pub extern "C" fn print_registers(machine: &crate::machine::Armv8AMachine) {
        tracing::event!(
            target: crate::tracing::TraceItem::BlockEntry.as_str(),
            tracing::Level::TRACE,
            "entering block pc = 0x{:x}, prev_pc = 0x{:x} with registers: {:?}",
            machine.pc,
            machine.prev_pc,
            RegisterFileDebug(&machine.cpu_state.registers)
        );
    }

    struct RegisterFileDebug<'a>(&'a crate::cpu_state::RegisterFile);

    impl<'a> std::fmt::Debug for RegisterFileDebug<'a> {
        fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
            let mut f = fmt.debug_struct("RegisterFile");
            macro_rules! print_reg {
                ($($reg:ident),*$(,)?) => {{
                    $(f.field(stringify!($reg), &format_args!("0x{:x}", self.0.$reg));)*
                }};
            }
            print_reg! {x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, sp, pstate};
            let pstate: crate::cpu_state::PSTATE = self.0.pstate.into();
            f.field("PSTATE", &pstate);
            f.finish()
        }
    }
}
pub use helpers::*;

#[derive(Copy, Clone, Ord, PartialOrd, PartialEq, Eq, Debug, clap::ValueEnum)]
/// Trace item targets
pub enum TraceItem {
    /// Logs an address lookup.
    AddressLookup,
    /// Logs registers when entering a translated block.
    BlockEntry,
    /// Enables `cranelift_codegen` crate tracing.
    CraneliftCodegen,
    /// Enables `cranelift_frontend` crate tracing.
    CraneliftFrontend,
    /// Enables `cranelift_jit` crate tracing.
    CraneliftJit,
    /// Logs exceptions.
    Exception,
    /// Logs gdb related events.
    Gdb,
    /// Logs `gdbstub` crate tracing.
    Gdbstub,
    /// Logs `aarch64` assembly of translated blocks.
    InAsm,
    /// Logs JIT related events.
    Jit,
    /// Logs lookup of translated blocks.
    LookupBlock,
    /// Logs memory accesses.
    Memory,
    /// Logs [`PL011State`](crate::devices::pl011::PL011State`) related events.
    Pl011,
}

impl TraceItem {
    /// All [`TraceItem`] variants.
    pub const POSSIBLE_VALUES: &[Self] = &[
        Self::AddressLookup,
        Self::BlockEntry,
        Self::CraneliftCodegen,
        Self::CraneliftFrontend,
        Self::CraneliftJit,
        Self::Exception,
        Self::Gdb,
        Self::Gdbstub,
        Self::InAsm,
        Self::Jit,
        Self::LookupBlock,
        Self::Memory,
        Self::Pl011,
    ];

    /// Target path of item.
    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::AddressLookup => "simulans::address_lookup",
            Self::BlockEntry => "simulans::block_entry",
            Self::CraneliftCodegen => "cranelift_codegen",
            Self::CraneliftFrontend => "cranelift_frontend",
            Self::CraneliftJit => "cranelift_jit",
            Self::Exception => "simulans::exception",
            Self::Gdb => "simulans::gdb",
            Self::Gdbstub => "gdbstub",
            Self::InAsm => "simulans::in_asm",
            Self::Jit => "simulans::jit",
            Self::LookupBlock => "simulans::lookup_block",
            Self::Memory => "simulans::memory",
            Self::Pl011 => "simulans::pl011",
        }
    }

    /// Snake case representation of item.
    pub const fn name(&self) -> &'static str {
        match self {
            Self::AddressLookup => "address_lookup",
            Self::BlockEntry => "block_entry",
            Self::CraneliftCodegen => "cranelift_codegen",
            Self::CraneliftFrontend => "cranelift_frontend",
            Self::CraneliftJit => "cranelift_jit",
            Self::Exception => "exception",
            Self::Gdb => "gdb",
            Self::Gdbstub => "gdbstub",
            Self::InAsm => "in_asm",
            Self::Jit => "jit",
            Self::LookupBlock => "lookup_block",
            Self::Memory => "memory",
            Self::Pl011 => "pl011",
        }
    }
}

impl std::fmt::Display for TraceItem {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "{}", self.name())
    }
}

impl std::str::FromStr for TraceItem {
    type Err = Box<dyn std::error::Error>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        for i in Self::POSSIBLE_VALUES.iter() {
            if i.as_str() == s {
                return Ok(*i);
            }
        }
        Err(Box::<dyn std::error::Error>::from(format!(
            "Expected one of {}",
            Self::POSSIBLE_VALUES
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<&str>>()
                .join(", ")
        )))
    }
}

impl std::ops::Deref for TraceItem {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

#[derive(Debug)]
/// Output of trace logs.
pub enum Output {
    /// Standard output.
    Stdout,
    /// Standard error.
    Stderr,
    /// File.
    File(std::fs::File),
}

impl std::io::Write for Output {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Self::Stdout => {
                let mut lck = std::io::stdout().lock();
                lck.write(buf)
            }
            Self::Stderr => {
                let mut lck = std::io::stderr().lock();
                lck.write(buf)
            }
            Self::File(ref mut f) => f.write(buf),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Self::Stdout => {
                let mut lck = std::io::stdout().lock();
                lck.flush()
            }
            Self::Stderr => {
                let mut lck = std::io::stderr().lock();
                lck.flush()
            }
            Self::File(ref mut f) => f.flush(),
        }
    }
}

/// Tracing guard
///
/// Tracing will stop when dropped.
pub struct TracingGuard {
    current_level: Cell<LevelFilter>,
    events: Arc<Mutex<BTreeSet<TraceItem>>>,
    #[allow(dead_code)]
    worker_guard: tracing_appender::non_blocking::WorkerGuard,
    reload_handle: tracing_subscriber::reload::Handle<
        tracing_subscriber::EnvFilter,
        tracing_subscriber::Registry,
    >,
}

impl TracingGuard {
    /// Returns current tracing level.
    pub fn current_level(&self) -> LevelFilter {
        self.current_level.get()
    }

    /// Returns current trace items.
    pub fn events(&self) -> impl std::ops::Deref<Target = BTreeSet<TraceItem>> + use<'_> {
        self.events.lock().unwrap()
    }

    /// Updates trace items.
    pub fn set_events(
        &self,
        events: BTreeSet<TraceItem>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        *self.events.lock().unwrap() = events;
        self.change_level(self.current_level())
    }

    /// Updates tracing level.
    pub fn change_level(&self, value: LevelFilter) -> Result<(), Box<dyn std::error::Error>> {
        let new_filter = Self::generate_env_filter(value, &self.events.lock().unwrap());
        self.reload_handle.modify(|filter| {
            *filter = new_filter;
        })?;
        Ok(())
    }

    /// Helper function to regenerate filter based on levels and events.
    fn generate_env_filter(
        level: LevelFilter,
        events: &BTreeSet<TraceItem>,
    ) -> tracing_subscriber::EnvFilter {
        let mut env_filter = tracing_subscriber::EnvFilter::builder()
            .with_default_directive(level.into())
            .from_env()
            .unwrap_or_default();
        for item in TraceItem::POSSIBLE_VALUES {
            env_filter = if events.contains(item) {
                env_filter.add_directive(format!("{}=trace", item.as_str()).parse().unwrap())
            } else {
                env_filter.add_directive(format!("{}=off", item.as_str()).parse().unwrap())
            };
        }
        env_filter
    }

    #[must_use]
    /// Creates a new [`TracingGuard`].
    pub fn init(
        log_level: LevelFilter,
        output: Output,
        ansi: bool,
        events: BTreeSet<TraceItem>,
    ) -> Self {
        let env_filter = Self::generate_env_filter(log_level, &events);
        let (env_filter, reload_handle) = reload::Layer::new(env_filter);
        let (log_layer, worker_guard) = match output {
            Output::File(_) => {
                let (non_blocking, worker_guard) = tracing_appender::non_blocking(output);
                (
                    tracing_subscriber::fmt::layer()
                        .with_thread_ids(true)
                        .with_thread_names(true)
                        .with_writer(non_blocking)
                        .with_ansi(false)
                        .and_then(env_filter)
                        .boxed(),
                    worker_guard,
                )
            }
            Output::Stdout => {
                let (non_blocking, worker_guard) = tracing_appender::non_blocking(output);
                (
                    tracing_subscriber::fmt::layer()
                        .pretty()
                        .with_writer(non_blocking)
                        .with_ansi(ansi)
                        .and_then(env_filter)
                        .boxed(),
                    worker_guard,
                )
            }
            Output::Stderr => {
                let (non_blocking, worker_guard) = tracing_appender::non_blocking(Output::Stderr);
                (
                    tracing_subscriber::fmt::layer()
                        .with_writer(non_blocking)
                        .with_ansi(false)
                        .and_then(env_filter)
                        .boxed(),
                    worker_guard,
                )
            }
        };

        tracing_subscriber::registry().with(log_layer).init();
        Self {
            events: Arc::new(Mutex::new(events)),
            current_level: log_level.into(),
            worker_guard,
            reload_handle,
        }
    }
}
