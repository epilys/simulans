// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! # Emulated devices
//!
//! Devices must implement the [`Device`] trait.

pub mod gicv2;
pub mod pl011;
use crate::memory::MemoryRegion;

/// Trait for device operations.
pub trait Device: std::fmt::Debug {
    /// Returns device ID.
    fn id(&self) -> u64;
    /// Returns device I/O memory regions.
    fn into_memory_regions(self) -> Vec<MemoryRegion>;
}

pub mod tube {
    //! Tube testing device (Memory mapped register)

    use std::sync::{
        atomic::{AtomicU8, Ordering},
        Arc,
    };

    use crate::memory::{Address, MemoryRegion, MemorySize, Width};

    #[derive(Debug)]
    /// Tube testing device (Memory mapped register) to signal shutdown for
    /// tests.
    pub struct Tube {
        /// Unique device ID.
        pub device_id: u64,
        pub address: Address,
        /// Atomic integer to alert machine of poweroff request.
        pub poweroff_request: Arc<AtomicU8>,
    }

    impl Tube {
        /// Create a new tube device that will write to `poweroff_request`.
        pub const fn new(
            device_id: u64,
            address: Address,
            poweroff_request: Arc<AtomicU8>,
        ) -> Self {
            Self {
                device_id,
                address,
                poweroff_request,
            }
        }
    }

    impl crate::devices::Device for Tube {
        fn id(&self) -> u64 {
            self.device_id
        }

        fn into_memory_regions(self) -> Vec<MemoryRegion> {
            let Self {
                device_id,
                address,
                poweroff_request,
            } = self;
            vec![MemoryRegion::new_io(
                MemorySize::new(0x100).unwrap(),
                address,
                Box::new(TubeOps {
                    device_id,
                    poweroff_request,
                }),
            )
            .unwrap()]
        }
    }

    #[derive(Debug)]
    struct TubeOps {
        device_id: u64,
        poweroff_request: Arc<AtomicU8>,
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
            self.poweroff_request.store(value as u8, Ordering::SeqCst);
        }
    }
}
