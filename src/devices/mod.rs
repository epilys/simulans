// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! # Emulated devices
//!
//! Devices must implement the [`Device`] trait.

pub mod pl011;
use crate::memory::DeviceMemoryOps;

/// Trait for device operations.
pub trait Device: std::fmt::Debug {
    /// Returns device ID.
    fn id(&self) -> u64;
    /// Returns device operations.
    fn ops(&self) -> Box<dyn DeviceMemoryOps>;
}

pub mod tube {
    //! Tube testing device (Memory mapped register)

    use std::sync::{
        atomic::{AtomicU8, Ordering},
        Arc,
    };

    use crate::memory::Width;

    #[derive(Debug)]
    /// Tube testing device (Memory mapped register) to signal shutdown for
    /// tests.
    pub struct Tube {
        /// Unique device ID.
        pub device_id: u64,
        /// Atomic integer to alert machine of exit request.
        pub exit_request: Arc<AtomicU8>,
    }

    impl Tube {
        /// Create a new tube device that will write to `exit_request`.
        pub const fn new(device_id: u64, exit_request: Arc<AtomicU8>) -> Self {
            Self {
                device_id,
                exit_request,
            }
        }
    }

    impl crate::devices::Device for Tube {
        fn id(&self) -> u64 {
            self.device_id
        }

        fn ops(&self) -> Box<dyn crate::memory::DeviceMemoryOps> {
            Box::new(TubeOps {
                device_id: self.device_id,
                exit_request: Arc::clone(&self.exit_request),
            })
        }
    }

    #[derive(Debug)]
    struct TubeOps {
        device_id: u64,
        exit_request: Arc<AtomicU8>,
    }

    impl crate::memory::DeviceMemoryOps for TubeOps {
        fn id(&self) -> u64 {
            self.device_id
        }

        fn read(&self, _offset: u64, _width: Width) -> u64 {
            0
        }

        fn write(&self, offset: u64, value: u64, width: Width) {
            eprintln!("write {offset:x}? {value:?} {width:?}");
            assert_eq!((width, offset), (Width::_8, 0));
            self.exit_request.store(value as u8, Ordering::SeqCst);
        }
    }
}
