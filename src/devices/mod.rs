// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! # Emulated devices
//!
//! Devices must implement the [`Device`] trait.

pub mod gicv2;
pub mod pl011;
pub mod timer;

use crate::memory::{MemoryRegion, Width};

/// Trait for device operations.
pub trait Device: std::fmt::Debug {
    /// Returns device ID.
    fn id(&self) -> u64;
    /// Returns device I/O memory regions.
    fn into_memory_regions(self) -> Vec<MemoryRegion>;
}

pub type MemoryTxResult<T = ()> = Result<T, crate::cpu_state::ExitRequest>;

pub trait CharBackendExt: DeviceOps {
    fn receive(&self, buf: &[u8]);
}

/// Trait for device memory operations.
pub trait DeviceOps: std::fmt::Debug + Send + Sync {
    /// Returns unique device ID.
    fn id(&self) -> u64;
    /// Performs a read.
    fn read(&self, address_inside_region: u64, width: Width) -> MemoryTxResult<u64>;
    /// Performs a write.
    fn write(&self, address_inside_region: u64, value: u64, width: Width) -> MemoryTxResult;

    #[inline(always)]
    fn supports_char_backend(&'_ self) -> Option<CharBackendOps<'_>> {
        // disabled by default
        None
    }

    #[inline(always)]
    fn supports_device_tree(&'_ self) -> Option<DeviceTreeOps<'_>> {
        // disabled by default
        None
    }
}

pub use crate::fdt::DeviceTreeExt;
pub type CharBackendOps<'a> = &'a dyn CharBackendExt;
pub type DeviceTreeOps<'a> = &'a dyn DeviceTreeExt;

impl PartialEq for &dyn DeviceOps {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for &dyn DeviceOps {}

pub mod tube {
    //! Tube testing device (Memory mapped register)

    use crate::{
        cpu_state::ExitRequest,
        devices::{DeviceOps, MemoryTxResult},
        memory::{Address, MemoryRegion, MemorySize, Width},
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
                0,
                Box::new(TubeOps { device_id }),
            )
            .unwrap()]
        }
    }

    #[derive(Debug)]
    struct TubeOps {
        device_id: u64,
    }

    impl DeviceOps for TubeOps {
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
