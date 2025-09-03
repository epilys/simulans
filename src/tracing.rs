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

use std::{
    cell::Cell,
    collections::BTreeSet,
    sync::{Arc, Mutex},
};

pub use ::tracing::{error, event, info, trace, warn};
pub use tracing_subscriber::filter::LevelFilter;
use tracing_subscriber::{prelude::*, reload, Layer};

#[derive(Copy, Clone, Ord, PartialOrd, PartialEq, Eq, Debug, clap::ValueEnum)]
pub enum TraceItem {
    AddressLookup,
    BlockEntry,
    BlockExit,
    CraneliftCodegen,
    CraneliftFrontend,
    CraneliftJit,
    Exception,
    Gdb,
    Jit,
    LookupEntry,
    Memory,
    Pl011,
}

impl TraceItem {
    pub const POSSIBLE_VALUES: &[Self] = &[
        Self::AddressLookup,
        Self::BlockEntry,
        Self::BlockExit,
        Self::CraneliftCodegen,
        Self::CraneliftFrontend,
        Self::CraneliftJit,
        Self::Exception,
        Self::Gdb,
        Self::Jit,
        Self::LookupEntry,
        Self::Memory,
        Self::Pl011,
    ];

    pub const fn as_str(&self) -> &'static str {
        match self {
            Self::AddressLookup => "address_lookup",
            Self::BlockEntry => "block_entry",
            Self::BlockExit => "block_exit",
            Self::CraneliftCodegen => "cranelift_codegen",
            Self::CraneliftFrontend => "cranelift_frontend",
            Self::CraneliftJit => "cranelift_jit",
            Self::Exception => "exception",
            Self::Gdb => "gdb",
            Self::Jit => "jit",
            Self::LookupEntry => "lookup_entry",
            Self::Memory => "memory",
            Self::Pl011 => "pl011",
        }
    }
}

impl std::fmt::Display for TraceItem {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(fmt, "{}", self.as_str())
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

#[derive(Debug)]
pub enum Output {
    Stdout,
    Stderr,
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
    pub fn current_level(&self) -> LevelFilter {
        self.current_level.get()
    }

    pub fn events(&self) -> impl std::ops::Deref<Target = BTreeSet<TraceItem>> + use<'_> {
        self.events.lock().unwrap()
    }

    pub fn set_events(
        &self,
        events: BTreeSet<TraceItem>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        *self.events.lock().unwrap() = events;
        self.change_level(self.current_level())
    }

    pub fn change_level(&self, value: LevelFilter) -> Result<(), Box<dyn std::error::Error>> {
        let new_filter = Self::generate_env_filter(value, &self.events.lock().unwrap());
        self.reload_handle.modify(|filter| {
            *filter = new_filter;
        })?;
        Ok(())
    }

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
                env_filter.add_directive(format!("{item}=trace").parse().unwrap())
            } else {
                env_filter.add_directive(format!("{item}=off").parse().unwrap())
            };
        }
        env_filter
    }
}

#[must_use]
pub fn init(
    log_level: LevelFilter,
    output: Output,
    ansi: bool,
    events: BTreeSet<TraceItem>,
) -> TracingGuard {
    let env_filter = TracingGuard::generate_env_filter(log_level, &events);
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
    TracingGuard {
        events: Arc::new(Mutex::new(events)),
        current_level: log_level.into(),
        worker_guard,
        reload_handle,
    }
}
