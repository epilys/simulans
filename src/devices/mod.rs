//
// simulans
//
// Copyright 2025 Emmanouil Pitsidianakis <manos@pitsidianak.is>
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

pub mod pl011;
use crate::memory::DeviceMemoryOps;

pub trait Device: std::fmt::Debug {
    fn id(&self) -> u64;
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
    pub struct Tube {
        pub device_id: u64,
        pub exit_request: Arc<AtomicU8>,
    }

    impl Tube {
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
        pub exit_request: Arc<AtomicU8>,
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
