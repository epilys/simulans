// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later

use vm_memory::{ByteValued, Le16, Le64};

// virtqueues

pub const REQUEST_QUEUE_IDX: u16 = 0;
pub const ALARM_QUEUE_IDX: u16 = 1;
pub const NUM_QUEUES: u16 = 2;

pub const VIRTIO_RTC_F_ALARM: u32 = 0;

/// common request header
#[doc(alias = "virtio_rtc_req_head")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcReqHead {
    pub msg_type: Le16,
    pub reserved: [u8; 6],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcReqHead {}

/// common response header
#[doc(alias = "virtio_rtc_resp_head")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcRespHead {
    pub status: u8,
    pub reserved: [u8; 7],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcRespHead {}

pub const VIRTIO_RTC_S_OK: u8 = 0;
pub const VIRTIO_RTC_S_EOPNOTSUPP: u8 = 2;
pub const VIRTIO_RTC_S_ENODEV: u8 = 3;
pub const VIRTIO_RTC_S_EINVAL: u8 = 4;
pub const VIRTIO_RTC_S_EIO: u8 = 5;

// Clock types:

pub const VIRTIO_RTC_CLOCK_UTC: u8 = 0;
pub const VIRTIO_RTC_CLOCK_TAI: u8 = 1;
pub const VIRTIO_RTC_CLOCK_MONOTONIC: u8 = 2;
pub const VIRTIO_RTC_CLOCK_UTC_SMEARED: u8 = 3;
pub const VIRTIO_RTC_CLOCK_UTC_MAYBE_SMEARED: u8 = 4;

// Smearing Variants

pub const VIRTIO_RTC_SMEAR_UNSPECIFIED: u8 = 0;
pub const VIRTIO_RTC_SMEAR_NOON_LINEAR: u8 = 1;
pub const VIRTIO_RTC_SMEAR_UTC_SLS: u8 = 2;

// Hardware counters

/// Arm Generic Timer Counter-timer Virtual Count Register (`CNTVCT_EL0`)
pub const VIRTIO_RTC_COUNTER_ARM_VCT: u8 = 0;
/// x86 Time-Stamp Counter
pub const VIRTIO_RTC_COUNTER_X86_TSC: u8 = 1;
/// Invalid
pub const VIRTIO_RTC_COUNTER_INVALID: u8 = 0xFF;

// Control Requests

/// Discovers the number of clocks
pub const VIRTIO_RTC_REQ_CFG: u16 = 0x1000;

#[doc(alias = "virtio_rtc_req_cfg")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcReqCfg {
    pub head: VirtioRtcReqHead,
}

#[doc(alias = "virtio_rtc_resp_cfg")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcRespCfg {
    pub head: VirtioRtcRespHead,
    pub num_clocks: Le16,
    pub reserved: [u8; 6],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcRespCfg {}

/// Discovers the capabilities of the clock identified by the `clock_id` field.
pub const VIRTIO_RTC_REQ_CLOCK_CAP: u16 = 0x1001;

#[doc(alias = "virtio_rtc_req_clock_cap")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcReqClockCap {
    pub head: VirtioRtcReqHead,
    pub clock_id: Le16,
    pub reserved: [u8; 6],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcReqClockCap {}

#[doc(alias = "virtio_rtc_resp_clock_cap")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcRespClockCap {
    pub head: VirtioRtcRespHead,
    pub r#type: u8,
    pub leap_second_smearing: u8,
    pub flags: u8,
    pub reserved: [u8; 5],
}

/// If `VIRTIO_RTC_F_ALARM` has been negotiated, the `VIRTIO_RTC_FLAG_ALARM_CAP`
/// flag indicates that the clock supports an alarm.
pub const VIRTIO_RTC_FLAG_ALARM_CAP: u8 = 1;

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcRespClockCap {}

/// Discovers whether the device supports cross-timestamping for a particular
/// pair of clock and hardware counter.
pub const VIRTIO_RTC_REQ_CROSS_CAP: u16 = 0x1002;

#[doc(alias = "virtio_rtc_req_cross_cap")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcReqCrossCap {
    pub head: VirtioRtcReqHead,
    pub clock_id: Le16,
    pub hw_counter: u8,
    pub reserved: [u8; 5],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcReqCrossCap {}

#[doc(alias = "virtio_rtc_resp_cross_cap")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcRespCrossCap {
    pub head: VirtioRtcRespHead,
    pub flags: u8,
    pub reserved: [u8; 7],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcRespCrossCap {}

/// The clock supports cross-timestamping for the particular clock and hardware
/// counter.
pub const VIRTIO_RTC_FLAG_CROSS_CAP: u8 = 1;

/// Reads the clock identified by the `clock_id` field. The device supports this
/// request for every clock.
pub const VIRTIO_RTC_REQ_READ: u16 = 0x0001;

#[doc(alias = "virtio_rtc_req_read")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcReqRead {
    pub head: VirtioRtcReqHead,
    pub clock_id: Le16,
    pub reserved: [u8; 6],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcReqRead {}

#[doc(alias = "virtio_rtc_resp_read")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcRespRead {
    pub head: VirtioRtcRespHead,
    pub clock_reading: Le64,
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcRespRead {}

/// Returns a cross-timestamp for the clock identified by the `clock_id` field.
pub const VIRTIO_RTC_REQ_READ_CROSS: u16 = 0x0002;

#[doc(alias = "virtio_rtc_req_read_cross")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcReqReadCross {
    pub head: VirtioRtcReqHead,
    pub clock_id: Le16,
    pub hw_counter: u8,
    pub reserved: [u8; 5],
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcReqReadCross {}

#[doc(alias = "virtio_rtc_resp_read_cross")]
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct VirtioRtcRespReadCross {
    pub head: VirtioRtcRespHead,
    pub clock_reading: Le64,
    pub counter_cycles: Le64,
}

// SAFETY: This struct is plain-old-data.
unsafe impl ByteValued for VirtioRtcRespReadCross {}

use nix::time::{clock_gettime, ClockId};
pub use nix::{sys::time::TimeSpec, Result};

pub fn get_utc() -> Result<TimeSpec> {
    clock_gettime(ClockId::CLOCK_REALTIME)
}

pub fn get_tai() -> Result<TimeSpec> {
    clock_gettime(ClockId::CLOCK_TAI)
}

pub fn get_monotonic() -> Result<TimeSpec> {
    clock_gettime(ClockId::CLOCK_MONOTONIC)
}

#[derive(Debug)]
pub struct Rtc;

impl super::VirtioBackend for Rtc {
    const ID: super::DeviceType = super::DeviceType::Timer;
    const NUM_OF_QUEUES: usize = 1;

    fn process_requests(
        &mut self,
        queue_selection: u32,
        queue: &mut virtio_queue::Queue,
        desc_chain: virtio_queue::DescriptorChain<&crate::memory::MemoryMap>,
        mem: &crate::memory::MemoryMap,
    ) {
        use virtio_queue::QueueT;

        assert_eq!(queue_selection, 0);

        let mut reader = virtio_queue::Reader::new(mem, desc_chain.clone()).unwrap();
        let request = reader.read_obj::<VirtioRtcReqHead>().unwrap();
        let mut writer = desc_chain.clone().writer(mem).unwrap();

        let msg_type: u16 = u16::from(request.msg_type);

        let mut used_len = 0;
        match msg_type {
            self::VIRTIO_RTC_REQ_CFG => {
                let res = VirtioRtcRespCfg {
                    num_clocks: 3.into(),
                    ..Default::default()
                };
                writer.write_obj(res).unwrap();
                used_len += writer.bytes_written();
            }
            self::VIRTIO_RTC_REQ_CLOCK_CAP => {
                let mut reader = desc_chain.clone().reader(mem).unwrap();
                let request = reader.read_obj::<VirtioRtcReqClockCap>().unwrap();
                let mut res = VirtioRtcRespClockCap::default();
                match u16::from(request.clock_id) {
                    0 => {
                        res.r#type = VIRTIO_RTC_CLOCK_UTC;

                        writer.write_obj(res).unwrap();
                        used_len += writer.bytes_written();
                    }
                    1 => {
                        res.r#type = VIRTIO_RTC_CLOCK_TAI;

                        writer.write_obj(res).unwrap();
                        used_len += writer.bytes_written();
                    }
                    2 => {
                        res.r#type = VIRTIO_RTC_CLOCK_MONOTONIC;

                        writer.write_obj(res).unwrap();
                        used_len += writer.bytes_written();
                    }
                    _ => {
                        let resp = VirtioRtcRespHead {
                            status: VIRTIO_RTC_S_EINVAL,
                            ..VirtioRtcRespHead::default()
                        };
                        writer.write_obj(resp).unwrap();

                        used_len += writer.bytes_written();
                    }
                }
            }
            self::VIRTIO_RTC_REQ_READ => {
                let mut reader = desc_chain.clone().reader(mem).unwrap();
                let request = reader.read_obj::<VirtioRtcReqRead>().unwrap();
                let mut res = VirtioRtcRespRead::default();
                match u16::from(request.clock_id) {
                    0 => {
                        let spec = get_utc().unwrap();
                        let clock_reading = (spec.tv_nsec() + spec.tv_sec() * 1000000000) as u64;
                        res.clock_reading = clock_reading.into();

                        writer.write_obj(res).unwrap();
                        used_len += writer.bytes_written();
                    }
                    1 => {
                        let spec = get_tai().unwrap();
                        let clock_reading = (spec.tv_nsec() + spec.tv_sec() * 1000000000) as u64;
                        res.clock_reading = clock_reading.into();

                        writer.write_obj(res).unwrap();
                        used_len += writer.bytes_written();
                    }
                    2 => {
                        let spec = get_monotonic().unwrap();
                        let clock_reading = (spec.tv_nsec() + spec.tv_sec() * 1000000000) as u64;
                        res.clock_reading = clock_reading.into();

                        writer.write_obj(res).unwrap();
                        used_len += writer.bytes_written();
                    }
                    _ => {
                        let resp = VirtioRtcRespHead {
                            status: VIRTIO_RTC_S_EINVAL,
                            ..VirtioRtcRespHead::default()
                        };
                        writer.write_obj(resp).unwrap();

                        used_len += writer.bytes_written();
                    }
                }
            }
            self::VIRTIO_RTC_REQ_READ_CROSS => {
                let resp = VirtioRtcRespHead {
                    status: VIRTIO_RTC_S_EOPNOTSUPP,
                    ..VirtioRtcRespHead::default()
                };

                writer.write_obj(resp).unwrap();

                used_len += writer.bytes_written();
            }
            self::VIRTIO_RTC_REQ_CROSS_CAP => {
                let res = VirtioRtcRespCrossCap::default();

                writer.write_obj(res).unwrap();

                used_len += writer.bytes_written();
            }
            other => panic!("{other}"),
        }

        let used_len = match u32::try_from(used_len) {
            Ok(len) => len,
            Err(len) => {
                tracing::warn!("used_len {len} overflows u32");
                u32::MAX
            }
        };

        if queue
            .add_used(mem, desc_chain.head_index(), used_len)
            .is_err()
        {
            tracing::error!("Couldn't return used descriptors to the ring");
        }
    }

    fn config(&self, _offset: u32, _size: u32) -> Vec<u8> {
        vec![]
    }
}
