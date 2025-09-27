// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! # Emulated devices
//!
//! Devices must implement the [`Device`] trait.

pub mod gicv2;
pub mod pl011;
pub mod timer;
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

    use crate::{
        cpu_state::ExitRequest,
        memory::{Address, DeviceMemoryOps, MemoryRegion, MemorySize, MemoryTxResult, Width},
    };

    #[derive(Debug)]
    /// Tube testing device (Memory mapped register) to signal shutdown for
    /// tests.
    pub struct Tube {
        /// Unique device ID.
        pub device_id: u64,
        pub address: Address,
    }

    impl Tube {
        /// Create a new tube device that will write request power off if `1` is
        /// written to it
        pub const fn new(device_id: u64, address: Address) -> Self {
            Self { device_id, address }
        }
    }

    impl crate::devices::Device for Tube {
        fn id(&self) -> u64 {
            self.device_id
        }

        fn into_memory_regions(self) -> Vec<MemoryRegion> {
            let Self { device_id, address } = self;
            vec![MemoryRegion::new_io(
                MemorySize::new(0x100).unwrap(),
                address,
                Box::new(TubeOps { device_id }),
            )
            .unwrap()]
        }
    }

    #[derive(Debug)]
    struct TubeOps {
        device_id: u64,
    }

    impl DeviceMemoryOps for TubeOps {
        fn id(&self) -> u64 {
            self.device_id
        }

        fn read(&self, _offset: u64, _width: Width) -> MemoryTxResult<u64> {
            Ok(0)
        }

        fn write(&self, offset: u64, value: u64, width: Width) -> MemoryTxResult {
            assert_eq!((width, offset), (Width::_8, 0));
            if value == 1 {
                return Err(ExitRequest::Poweroff);
            }
            Ok(())
        }
    }
}
