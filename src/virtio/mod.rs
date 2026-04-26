// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! VIRTIO device backend implementations

pub const VIRTIO_F_VERSION_1: u32 = 32;

pub trait VirtioBackend: std::fmt::Debug + Send + Sync + 'static {
    const ID: DeviceType;
    const NUM_OF_QUEUES: usize;
    const MAX_QUEUE_SIZE: u32 = 128;

    fn process_requests(
        &mut self,
        queue_selection: u32,
        queue: &mut virtio_queue::Queue,
        desc_chain: virtio_queue::DescriptorChain<&crate::memory::MemoryMap>,
        mem: &crate::memory::MemoryMap,
    );

    fn device_features(&self) -> u64 {
        1 << VIRTIO_F_VERSION_1
    }

    fn config(&self, offset: u32, size: u32) -> Vec<u8>;
}

/// VIRTIO Device Type
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum DeviceType {
    Invalid = 0,
    Network = 1,
    Block = 2,
    Console = 3,
    EntropySource = 4,
    MemoryBallooning = 5,
    IoMemory = 6,
    Rpmsg = 7,
    ScsiHost = 8,
    _9P = 9,
    Mac80211 = 10,
    RprocSerial = 11,
    VirtioCAIF = 12,
    MemoryBalloon = 13,
    GPU = 16,
    Timer = 17,
    Input = 18,
    Socket = 19,
    Crypto = 20,
    SignalDistributionModule = 21,
    Pstore = 22,
    IOMMU = 23,
    Memory = 24,
    Sound = 25,
}

impl From<u32> for DeviceType {
    fn from(virtio_device_id: u32) -> Self {
        match virtio_device_id {
            1 => Self::Network,
            2 => Self::Block,
            3 => Self::Console,
            4 => Self::EntropySource,
            5 => Self::MemoryBalloon,
            6 => Self::IoMemory,
            7 => Self::Rpmsg,
            8 => Self::ScsiHost,
            9 => Self::_9P,
            10 => Self::Mac80211,
            11 => Self::RprocSerial,
            12 => Self::VirtioCAIF,
            13 => Self::MemoryBalloon,
            16 => Self::GPU,
            17 => Self::Timer,
            18 => Self::Input,
            19 => Self::Socket,
            20 => Self::Crypto,
            21 => Self::SignalDistributionModule,
            22 => Self::Pstore,
            23 => Self::IOMMU,
            24 => Self::Memory,
            25 => Self::Sound,
            _ => Self::Invalid,
        }
    }
}

impl From<u16> for DeviceType {
    fn from(virtio_device_id: u16) -> Self {
        u32::from(virtio_device_id).into()
    }
}

impl From<u8> for DeviceType {
    fn from(virtio_device_id: u8) -> Self {
        u32::from(virtio_device_id).into()
    }
}
