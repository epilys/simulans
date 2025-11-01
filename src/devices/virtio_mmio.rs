// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! VIRTIO MMIO transport

use std::{
    collections::BTreeMap,
    sync::{Arc, Mutex},
};

use crate::{
    devices::{DeviceOps, MemoryTxResult},
    machine::interrupts::{InterruptGenerator, Interrupts},
    memory::{Address, DeviceID, MemoryRegion, MemorySize, ServiceRequestNotifier, Width},
    virtio::{DeviceType, VirtioBackend},
};

#[derive(Debug)]
pub struct VirtioMMIO<B: VirtioBackend> {
    backend: B,
    device_id: DeviceID,
    virtio_device_id: DeviceType,
    virtio_vendor_id: Option<u32>,
    state: VirtioMMIOState,
    address: Address,
    request_notifier: crate::memory::ServiceRequestNotifier,
    interrupt_id: u16,
    irq_generator: InterruptGenerator,
}

impl<B: VirtioBackend> crate::devices::Device for VirtioMMIO<B> {
    fn id(&self) -> DeviceID {
        self.device_id
    }

    fn into_memory_regions(self) -> Vec<MemoryRegion> {
        let Self {
            backend,
            device_id,
            virtio_device_id,
            virtio_vendor_id,
            mut state,
            address,
            interrupt_id,
            request_notifier,
            irq_generator,
        } = self;
        let config = backend.config(0, 0x100);
        let len = config.len().min(0x100);
        state.config[..len].copy_from_slice(&config[..len]);

        vec![MemoryRegion::new_io(
            MemorySize::new(0x200).unwrap(),
            address,
            0,
            Box::new(VirtioMMIOMemoryOps {
                backend: Arc::new(Mutex::new(backend)),
                device_id,
                virtio_device_id,
                virtio_vendor_id,
                interrupt_id,
                state: Arc::new(Mutex::new(state)),
                device: Arc::new(Mutex::new(BTreeMap::default())),
                request_notifier,
                irq_generator,
            }),
        )
        .unwrap()]
    }
}

#[derive(Debug, Clone, Default)]
pub struct VirtioQueueConfig {
    size: u32,
    size_max: u32,
    desc_address: u64,
    driver_area_address: u64,
    device_area_address: u64,
    ready: bool,
}

#[derive(Debug)]
struct VirtioMMIOState {
    status_flags: u32,
    device_features: u64,
    device_features_select_hi: bool,
    driver_features: u64,
    driver_features_select_hi: bool,
    queue_selection: u32,
    config: [u8; 0x100],
    queues: Vec<VirtioQueueConfig>,
    interrupt_status_used_buffer: bool,
    interrupt_status_configuration_changed: bool,
}

impl Default for VirtioMMIOState {
    fn default() -> Self {
        Self {
            status_flags: 0,
            device_features: 0,
            device_features_select_hi: false,
            driver_features: 0,
            driver_features_select_hi: false,
            queue_selection: 0,
            config: [0; 0x100],
            queues: vec![],
            interrupt_status_used_buffer: false,
            interrupt_status_configuration_changed: false,
        }
    }
}

impl VirtioMMIOState {
    fn queue_size_max(&self) -> Option<u32> {
        let q = self.queues.get(self.queue_selection as usize)?;
        Some(q.size_max)
    }

    fn queue_size(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.size = value;
    }

    fn queue_ready(&self) -> Option<bool> {
        let q = self.queues.get(self.queue_selection as usize)?;
        Some(q.ready)
    }

    fn set_queue_ready(
        &mut self,
        value: bool,
        device_id: DeviceID,
        request_notifier: &ServiceRequestNotifier,
    ) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        let queue_selection = self.queue_selection;
        if q.ready && !value {
            request_notifier
                .send(crate::memory::ServiceRequest::VirtioQueueNotReady {
                    device_id,
                    queue_selection,
                })
                .unwrap();
        } else if !q.ready && value {
            request_notifier
                .send(crate::memory::ServiceRequest::VirtioQueueReady {
                    device_id,
                    queue_selection,
                    size: q.size,
                    size_max: q.size_max,
                    desc_address: q.desc_address,
                    driver_area_address: q.driver_area_address,
                    device_area_address: q.device_area_address,
                })
                .unwrap();
        }
        q.ready = value;
    }

    fn set_queue_desc_low(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.desc_address &= !(u64::from(u32::MAX));
        q.desc_address |= u64::from(value);
    }

    fn set_queue_desc_high(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.desc_address &= !(u64::from(u32::MAX) << 32);
        q.desc_address |= u64::from(value) << 32;
    }

    fn set_queue_driver_low(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.driver_area_address &= !(u64::from(u32::MAX));
        q.driver_area_address |= u64::from(value);
    }

    fn set_queue_driver_high(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.driver_area_address &= !(u64::from(u32::MAX) << 32);
        q.driver_area_address |= u64::from(value) << 32;
    }

    fn set_queue_device_low(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.device_area_address &= !(u64::from(u32::MAX));
        q.device_area_address |= u64::from(value);
    }

    fn set_queue_device_high(&mut self, value: u32) {
        let Some(q) = self.queues.get_mut(self.queue_selection as usize) else {
            return;
        };
        q.device_area_address &= !(u64::from(u32::MAX) << 32);
        q.device_area_address |= u64::from(value) << 32;
    }

    fn queue_notify(
        &self,
        _value: u32,
        device_id: DeviceID,
        request_notifier: &ServiceRequestNotifier,
    ) {
        if self.queues.get(self.queue_selection as usize).is_none() {
            return;
        }
        request_notifier
            .send(crate::memory::ServiceRequest::VirtioQueueNotify {
                device_id,
                queue_selection: self.queue_selection,
            })
            .unwrap();
    }
}

#[derive(Debug)]
struct VirtioMMIOMemoryOps<B: VirtioBackend> {
    backend: Arc<Mutex<B>>,
    device_id: DeviceID,
    virtio_device_id: DeviceType,
    virtio_vendor_id: Option<u32>,
    state: Arc<Mutex<VirtioMMIOState>>,
    device: Arc<Mutex<BTreeMap<u32, virtio_queue::Queue>>>,
    request_notifier: crate::memory::ServiceRequestNotifier,
    interrupt_id: u16,
    irq_generator: InterruptGenerator,
}

impl<B: VirtioBackend> DeviceOps for VirtioMMIOMemoryOps<B> {
    fn id(&self) -> DeviceID {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> MemoryTxResult<u64> {
        if width >= Width::_64 && width != Width::_32 && !(0x100..0x200).contains(&offset) {
            // Non-compliant
            return Ok(0);
        }
        let value = match offset {
            0x000..0x004 => {
                // (a Little Endian equivalent of the “virt” string).
                Ok(0x74726976)
            }
            0x004..0x008 => {
                // Version

                // Device version number
                Ok(0x2)
            }
            0x008..0x00c => {
                // DeviceID
                Ok((self.virtio_device_id as u8).into())
            }
            0x00c..0x010 => {
                // VendorID
                Ok(self.virtio_vendor_id.unwrap_or(0).into())
            }
            0x010..0x014 => {
                // DeviceFeatures

                // Flags representing features the device supports
                // Reading from this register returns 32 consecutive flag bits, the least
                // significant bit depending on the last value written to DeviceFeaturesSel.
                // Access to this register returns bits DeviceFeaturesSel ∗ 32 to
                // (DeviceFeaturesSel ∗ 32) + 31, eg. feature bits 0 to 31 if DeviceFeaturesSel
                // is set to 0 and features bits 32 to 63 if DeviceFeaturesSel is set to 1. Also
                // see 2.2 Feature Bits.
                let state = self.state.lock().unwrap();
                if state.device_features_select_hi {
                    Ok(state.device_features >> 32)
                } else {
                    Ok(state.device_features & (u64::from(u32::MAX) << 32))
                }
            }
            0x014..0x020 => {
                // DeviceFeaturesSel Write-only
                Ok(0)
            }
            0x020..0x024 => {
                // DriverFeatures Write-only
                Ok(0)
            }
            0x024..0x028 => {
                // DriverFeaturesSel Write-only
                Ok(0)
            }
            0x028..0x030 => {
                // Reserved
                Ok(0)
            }
            0x030..0x034 => {
                // QueueSel Write-only
                // Virtqueue index
                // Writing to this register selects the virtqueue that the following operations
                // on QueueSizeMax, QueueSize, QueueReady, QueueDescLow, QueueDescHigh,
                // QueueDriverlLow, QueueDriverHigh, QueueDeviceLow, QueueDeviceHigh and
                // QueueReset apply to.
                Ok(0)
            }
            0x034..0x038 => {
                // QueueSizeMax

                // Maximum virtqueue size
                // Reading from the register returns the maximum size (number of elements) of
                // the queue the device is ready to process or zero (0x0) if the queue is not
                // available. This applies to the queue selected by writing to QueueSel. Note:
                // QueueSizeMax was previously known as QueueNumMax.
                let state = self.state.lock().unwrap();
                Ok(state.queue_size_max().unwrap_or(0).into())
            }
            0x038..0x03c => {
                // QueueSize Write-only
                // Virtqueue size
                // Queue size is the number of elements in the queue. Writing to this register
                // notifies the device what size of the queue the driver will use. This applies
                // to the queue selected by writing to QueueSel. Note: QueueSize was previously
                // known as QueueNum.
                Ok(0)
            }
            0x03c..0x044 => {
                // Reserved
                Ok(0)
            }
            0x044..0x048 => {
                // QueueReady RW

                // Virtqueue ready bit
                // Writing one (0x1) to this register notifies the device that it can execute
                // requests from this virtqueue. Reading from this register returns the last
                // value written to it. Both read and write accesses apply to the queue selected
                // by writing to QueueSel.
                let state = self.state.lock().unwrap();
                Ok(state.queue_ready().unwrap_or(false).into())
            }
            0x048..0x050 => {
                // Reserved
                Ok(0)
            }
            0x050..0x054 => {
                // QueueNotify Write-only
                // Queue notifier
                // Writing a value to this register notifies the device that there are new
                // buffers to process in a queue.

                // When VIRTIO_F_NOTIFICATION_DATA has not been negotiated, the value written is
                // the queue index.

                // When VIRTIO_F_NOTIFICATION_DATA has been negotiated, the Notification data
                // value has the following format:

                // le32 {
                //   vq_index: 16; /* previously known as vqn */
                //   next_off : 15;
                //   next_wrap : 1;
                // };

                Ok(0)
            }
            0x054..0x060 => {
                // Reserved
                Ok(0)
            }
            0x060..0x064 => {
                // InterruptStatus
                // Interrupt status
                // Reading from this register returns a bit mask of events that caused the
                // device interrupt to be asserted. The following events are possible:

                // Used Buffer Notification

                //     - bit 0 - the interrupt was asserted because the device has used a buffer
                //       in at least one of the active virtqueues.
                // Configuration Change Notification

                //     - bit 1 - the interrupt was asserted because the configuration of the
                //       device has changed.

                let state = self.state.lock().unwrap();
                let used_buffer = state.interrupt_status_used_buffer;
                let conf_changed = state.interrupt_status_configuration_changed;
                Ok(u64::from(used_buffer) | u64::from(conf_changed) << 1)
            }
            0x064..0x068 => {
                // InterruptACK Write-only

                // Interrupt acknowledge
                // Writing a value with bits set as defined in InterruptStatus to this register
                // notifies the device that events causing the interrupt have been handled.
                Ok(0)
            }
            0x068..0x070 => {
                // Reserved
                Ok(0)
            }
            0x070..0x074 => {
                // Device status
                Ok(self.state.lock().unwrap().status_flags.into())
            }
            0x074..0x080 => {
                // Reserved
                Ok(0)
            }
            0x080..0x084 => {
                // QueueDescLow W
                Ok(0)
            }
            0x084..0x088 => {
                // QueueDescHigh W
                // Virtqueue’s Descriptor Area 64 bit long physical address
                // Writing to these two registers (lower 32 bits of the address to QueueDescLow,
                // higher 32 bits to QueueDescHigh) notifies the device about location of the
                // Descriptor Area of the queue selected by writing to QueueSel register.
                Ok(0)
            }
            0x088..0x090 => {
                // Reserved
                Ok(0)
            }
            0x090..0x094 => {
                // QueueDriverLow W
                Ok(0)
            }
            0x094..0x098 => {
                // QueueDriverHigh W
                // Virtqueue’s Driver Area 64 bit long physical address
                // Writing to these two registers (lower 32 bits of the address to
                // QueueDriverLow, higher 32 bits to QueueDriverHigh) notifies the device about
                // location of the Driver Area of the queue selected by writing to QueueSel.
                Ok(0)
            }
            0x098..0x0a0 => {
                // Reserved
                Ok(0)
            }
            0x0a0..0x0a4 => {
                // QueueDeviceLow W
                Ok(0)
            }
            0x0a4..0x0a8 => {
                // QueueDeviceHigh W
                // Virtqueue’s Device Area 64 bit long physical address
                // Writing to these two registers (lower 32 bits of the address to
                // QueueDeviceLow, higher 32 bits to QueueDeviceHigh) notifies the device about
                // location of the Device Area of the queue selected by writing to QueueSel.
                Ok(0)
            }
            0x0a8..0x0ac => {
                // Reserved
                Ok(0)
            }
            0x0ac..0x0b0 => {
                // SHMSel W

                // Shared memory id
                // Writing to this register selects the shared memory region 2.10 following
                // operations on SHMLenLow, SHMLenHigh, SHMBaseLow and SHMBaseHigh apply to.
                Ok(0)
            }
            0x0b0..0x0b4 => {
                // SHMLenLow R
                Ok(0)
            }
            0x0b4..0x0b8 => {
                // SHMLenHigh
                Ok(0)

                // Shared memory region 64 bit long length
                // These registers return the length of the shared memory region
                // in bytes, as defined by the device for the region selected by
                // the SHMSel register. The lower 32 bits of the length are read
                // from SHMLenLow and the higher 32 bits from SHMLenHigh.
                // Reading from a non-existent region (i.e. where the ID written
                // to SHMSel is unused) results in a length of -1.
            }
            0x0b8..0x0bc => {
                // SHMBaseLow
                Ok(0)
            }
            0x0bc..0x0c0 => {
                // SHMBaseHigh
                Ok(0)

                // Shared memory region 64 bit long physical address
                // The driver reads these registers to discover the base address
                // of the region in physical address space. This address is
                // chosen by the device (or other part of the VMM). The lower 32
                // bits of the address are read from SHMBaseLow with the higher
                // 32 bits from SHMBaseHigh. Reading from a non-existent region
                // (i.e. where the ID written to SHMSel is unused) results in a
                // base address of 0xffffffffffffffff.
            }
            0x0c0..0x0c4 => {
                // QueueReset RW
                Ok(0)

                // Virtqueue reset bit
                // If VIRTIO_F_RING_RESET has been negotiated, writing one (0x1)
                // to this register selectively resets the queue. Both read and
                // write accesses apply to the queue selected by writing to
                // QueueSel.
            }
            0x0c4..0x0fc => {
                // Reserved
                Ok(0)
            }
            0x0fc..0x100 => {
                // ConfigGeneration

                // Configuration atomicity value
                // Reading from this register returns a value describing a version of the
                // device-specific configuration space (see Config). The driver can then access
                // the configuration space and, when finished, read ConfigGeneration again. If
                // no part of the configuration space has changed between these two
                // ConfigGeneration reads, the returned values are identical. If the values are
                // different, the configuration space accesses were not atomic and the driver
                // has to perform the operations again. See also 2.5.
                Ok(0)
            }
            0x100..0x200 => {
                // Config RW

                // Configuration space
                // Device-specific configuration space starts at the offset 0x100 and is
                // accessed with byte alignment. Its meaning and size depend on the device and
                // the driver.
                let state = self.state.lock().unwrap();
                let slice = &state.config[offset as usize - 0x100..];
                Ok(match width {
                    Width::_8 => slice[0].into(),
                    Width::_16 => u16::from_le_bytes([slice[0], slice[1]]).into(),
                    Width::_32 => {
                        u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]).into()
                    }
                    _ => unreachable!(),
                })
            }
            other => panic!("{other:#x}"),
        };

        //tracing::debug!("read offset {offset:#x} value {:#x}", value.unwrap());
        value
    }

    fn write(&self, offset: u64, value: u64, width: Width) -> MemoryTxResult {
        //tracing::debug!("write offset {offset:#x} value {value:#x}");
        if width >= Width::_64 && width != Width::_32 && !(0x100..0x200).contains(&offset) {
            // Non-compliant
            return Ok(());
        }
        match offset {
            0x000..0x004 => {
                // Ignore
            }
            0x004..0x008 => {
                // Ignore
            }
            0x008..0x00c => {
                // Ignore
            }
            0x00c..0x010 => {
                // Ignore
            }
            0x010..0x014 => {
                // Ignore
            }
            0x014..0x020 => {
                // DeviceFeaturesSel Write-only

                // Device (host) features word selection.
                // Writing to this register selects a set of 32 device feature bits accessible
                // by reading from DeviceFeatures.
                self.state.lock().unwrap().device_features_select_hi = value == 1;
            }
            0x020..0x024 => {
                // DriverFeatures Write-only

                // Flags representing device features understood and activated by the driver
                // Writing to this register sets 32 consecutive flag bits, the least significant
                // bit depending on the last value written to DriverFeaturesSel. Access to this
                // register sets bits DriverFeaturesSel ∗ 32 to (DriverFeaturesSel ∗ 32) + 31,
                // eg. feature bits 0 to 31 if DriverFeaturesSel is set to 0 and features bits
                // 32 to 63 if DriverFeaturesSel is set to 1. Also see 2.2 Feature Bits.
                let mut state = self.state.lock().unwrap();
                if state.driver_features_select_hi {
                    state.driver_features &= u64::from(u32::MAX) << 32;
                    state.driver_features |= value << 32;
                } else {
                    state.driver_features &= u64::from(u32::MAX);
                    state.driver_features |= value;
                }
            }
            0x024..0x028 => {
                // DriverFeaturesSel Write-only
                // Activated (guest) features word selection
                // Writing to this register selects a set of 32 activated feature bits
                // accessible by writing to DriverFeatures.
                self.state.lock().unwrap().driver_features_select_hi = value == 1;
            }
            0x028..0x030 => {
                // Reserved
                // Ignore
            }
            0x030..0x034 => {
                // QueueSel Write-only
                // Virtqueue index
                // Writing to this register selects the virtqueue that the following operations
                // on QueueSizeMax, QueueSize, QueueReady, QueueDescLow, QueueDescHigh,
                // QueueDriverlLow, QueueDriverHigh, QueueDeviceLow, QueueDeviceHigh and
                // QueueReset apply to.
                self.state.lock().unwrap().queue_selection = value as u32;
            }
            0x034..0x038 => {
                // QueueSizeMax
                // Ignore
            }
            0x038..0x03c => {
                // QueueSize Write-only
                // Virtqueue size
                // Queue size is the number of elements in the queue. Writing to this register
                // notifies the device what size of the queue the driver will use. This applies
                // to the queue selected by writing to QueueSel. Note: QueueSize was previously
                // known as QueueNum.
                self.state.lock().unwrap().queue_size(value as u32);
            }
            0x03c..0x044 => {
                // Reserved
                // Ignore
            }
            0x044..0x048 => {
                // QueueReady RW

                // Virtqueue ready bit
                // Writing one (0x1) to this register notifies the device that it can execute
                // requests from this virtqueue. Reading from this register returns the last
                // value written to it. Both read and write accesses apply to the queue selected
                // by writing to QueueSel.
                self.state.lock().unwrap().set_queue_ready(
                    value == 1,
                    self.device_id,
                    &self.request_notifier,
                );
            }
            0x048..0x050 => {
                // Reserved
                // Ignore
            }
            0x050..0x054 => {
                // QueueNotify Write-only
                // Queue notifier
                // Writing a value to this register notifies the device that there are new
                // buffers to process in a queue.

                // When VIRTIO_F_NOTIFICATION_DATA has not been negotiated, the value written is
                // the queue index.

                // When VIRTIO_F_NOTIFICATION_DATA has been negotiated, the Notification data
                // value has the following format:

                // le32 {
                //   vq_index: 16; /* previously known as vqn */
                //   next_off : 15;
                //   next_wrap : 1;
                // };

                self.state.lock().unwrap().queue_notify(
                    value as u32,
                    self.device_id,
                    &self.request_notifier,
                );
            }
            0x054..0x060 => {
                // Reserved
                // Ignore
            }
            0x060..0x064 => {
                // InterruptStatus
                // Ignore
            }
            0x064..0x068 => {
                // InterruptACK Write-only

                // Interrupt acknowledge
                // Writing a value with bits set as defined in InterruptStatus to this register
                // notifies the device that events causing the interrupt have been handled.
                let mut state = self.state.lock().unwrap();
                if state.interrupt_status_used_buffer {
                    state.interrupt_status_used_buffer = false;

                    _ = self.irq_generator.irq_sender.try_send(
                        crate::machine::interrupts::InterruptRequest {
                            interrupt_id: self.interrupt_id + 32,
                            cpu_id: None,
                            signal: false,
                        },
                    );
                }
            }
            0x068..0x070 => {
                // Reserved
                // Ignore
            }
            0x070..0x074 => {
                // Status RW
                // Device status
                // Reading from this register returns the current device status flags. Writing
                // non-zero values to this register sets the status flags, indicating the driver
                // progress. Writing zero (0x0) to this register triggers a device reset. See
                // also p. 4.2.3.1 Device Initialization.
                self.state.lock().unwrap().status_flags = value as u32;
            }
            0x074..0x080 => {
                // Reserved
                // Ignore
            }
            0x080..0x084 => {
                // QueueDescLow W
                self.state.lock().unwrap().set_queue_desc_low(value as u32);
            }
            0x084..0x088 => {
                // QueueDescHigh W
                // Virtqueue’s Descriptor Area 64 bit long physical address
                // Writing to these two registers (lower 32 bits of the address to QueueDescLow,
                // higher 32 bits to QueueDescHigh) notifies the device about location of the
                // Descriptor Area of the queue selected by writing to QueueSel register.
                self.state.lock().unwrap().set_queue_desc_high(value as u32);
            }
            0x088..0x090 => {
                // Reserved
                // Ignore
            }
            0x090..0x094 => {
                // QueueDriverLow W
                self.state
                    .lock()
                    .unwrap()
                    .set_queue_driver_low(value as u32);
            }
            0x094..0x098 => {
                // QueueDriverHigh W
                // Virtqueue’s Driver Area 64 bit long physical address
                // Writing to these two registers (lower 32 bits of the address to
                // QueueDriverLow, higher 32 bits to QueueDriverHigh) notifies the device about
                // location of the Driver Area of the queue selected by writing to QueueSel.
                self.state
                    .lock()
                    .unwrap()
                    .set_queue_driver_high(value as u32);
            }
            0x098..0x0a0 => {
                // Reserved
                // ignore
            }
            0x0a0..0x0a4 => {
                // QueueDeviceLow W
                self.state
                    .lock()
                    .unwrap()
                    .set_queue_device_low(value as u32);
            }
            0x0a4..0x0a8 => {
                // QueueDeviceHigh W
                // Virtqueue’s Device Area 64 bit long physical address
                // Writing to these two registers (lower 32 bits of the address to
                // QueueDeviceLow, higher 32 bits to QueueDeviceHigh) notifies the device about
                // location of the Device Area of the queue selected by writing to QueueSel.
                self.state
                    .lock()
                    .unwrap()
                    .set_queue_device_high(value as u32);
            }
            0x0a8..0x0ac => {
                // Reserved
                // Ignore
            }
            0x0ac..0x0b0 => {
                // SHMSel W

                // Shared memory id
                // Writing to this register selects the shared memory region 2.10 following
                // operations on SHMLenLow, SHMLenHigh, SHMBaseLow and SHMBaseHigh apply to.
                todo!()
            }
            0x0b0..0x0b4 => {
                // SHMLenLow R
                // Ignore
            }
            0x0b4..0x0b8 => {
                // SHMLenHigh
                // Ignore

                // Shared memory region 64 bit long length
                // These registers return the length of the shared memory region
                // in bytes, as defined by the device for the region selected by
                // the SHMSel register. The lower 32 bits of the length are read
                // from SHMLenLow and the higher 32 bits from SHMLenHigh.
                // Reading from a non-existent region (i.e. where the ID written
                // to SHMSel is unused) results in a length of -1.
            }
            0x0b8..0x0bc => {
                // SHMBaseLow
                // Ignore
            }
            0x0bc..0x0c0 => {
                // SHMBaseHigh
                // Ignore

                // Shared memory region 64 bit long physical address
                // The driver reads these registers to discover the base address
                // of the region in physical address space. This address is
                // chosen by the device (or other part of the VMM). The lower 32
                // bits of the address are read from SHMBaseLow with the higher
                // 32 bits from SHMBaseHigh. Reading from a non-existent region
                // (i.e. where the ID written to SHMSel is unused) results in a
                // base address of 0xffffffffffffffff.
            }
            0x0c0..0x0c4 => {
                // QueueReset RW
                todo!()

                // Virtqueue reset bit
                // If VIRTIO_F_RING_RESET has been negotiated, writing one (0x1)
                // to this register selectively resets the queue. Both read and
                // write accesses apply to the queue selected by writing to
                // QueueSel.
            }
            0x0c4..0x0fc => {
                // Reserved
                // Ignore
            }
            0x0fc..0x100 => {
                // ConfigGeneration

                // Configuration atomicity value
                // Reading from this register returns a value describing a
                // version of the device-specific configuration space (see
                // Config). The driver can then access the configuration space
                // and, when finished, read ConfigGeneration again. If no part
                // of the configuration space has changed between these two
                // ConfigGeneration reads, the returned values are identical. If
                // the values are different, the configuration space accesses
                // were not atomic and the driver has to perform the operations
                // again. See also 2.5. Ignore
            }
            0x100..0x200 => {
                // Config RW

                // Configuration space
                // Device-specific configuration space starts at the offset 0x100 and is
                // accessed with byte alignment. Its meaning and size depend on the device and
                // the driver.
                let mut state = self.state.lock().unwrap();

                let value = value.to_le_bytes();

                let slice = &mut state.config[offset as usize - 0x100..];
                match width {
                    Width::_8 => slice[0] = value[0],
                    Width::_16 => {
                        slice[0] = value[0];
                        slice[1] = value[1];
                    }
                    Width::_32 => {
                        slice[0] = value[0];
                        slice[1] = value[1];
                        slice[2] = value[2];
                        slice[3] = value[3];
                    }
                    _ => unreachable!(),
                }
            }
            other => panic!("{other:#x}"),
        }
        Ok(())
    }

    #[inline(always)]
    fn supports_device_tree(&'_ self) -> Option<crate::devices::DeviceTreeOps<'_>> {
        Some(self)
    }

    #[inline(always)]
    fn supports_virtio(&'_ self) -> Option<crate::devices::VirtioOps<'_>> {
        Some(self)
    }
}

impl<B: VirtioBackend> crate::devices::DeviceTreeExt for VirtioMMIOMemoryOps<B> {
    fn kind(&self) -> Option<crate::fdt::NodeKind> {
        Some(crate::fdt::NodeKind::Stdout("virtio_mmio".to_string()))
    }

    fn insert(
        &self,
        ctx: &crate::fdt::FdtContext,
        writer: &mut crate::fdt::FdtWriter,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let (start, len) = ctx
            .memory_regions
            .first()
            .map(|mr| (mr.phys_offset.0, mr.size.get()))
            .unwrap();
        assert_eq!(len, 0x200);

        let virtio_mmio_node = writer.begin_node(&format!("virtio_mmio@{start:x?}"))?;
        writer.property_null("dma-coherent")?;
        writer.property_array_u32("interrupts", &[0x00, self.interrupt_id.into(), 0x01])?;
        writer.property_array_u64("reg", &[start, len])?;
        writer.property_string_list("compatible", vec!["virtio,mmio".to_string()])?;
        writer.end_node(virtio_mmio_node)?;
        Ok(())
    }
}

impl<B: VirtioBackend> VirtioMMIO<B> {
    pub fn new(
        backend: B,
        device_id: DeviceID,
        virtio_vendor_id: Option<u32>,
        address: Address,
        request_notifier: crate::memory::ServiceRequestNotifier,
        interrupt_id: u16,
        interrupts: &Interrupts,
    ) -> Self {
        let virtio_device_id: DeviceType = B::ID;
        let irq_generator = interrupts.generator.clone();
        let state = VirtioMMIOState {
            device_features: backend.device_features(),
            queues: vec![
                VirtioQueueConfig {
                    size_max: B::MAX_QUEUE_SIZE,
                    ..Default::default()
                };
                B::NUM_OF_QUEUES
            ],
            ..VirtioMMIOState::default()
        };
        Self {
            backend,
            device_id,
            virtio_device_id,
            virtio_vendor_id,
            state,
            address,
            request_notifier,
            interrupt_id,
            irq_generator,
        }
    }
}

impl<B: VirtioBackend> crate::devices::VirtioExt for VirtioMMIOMemoryOps<B> {
    fn queue_set_ready(
        &self,
        queue_selection: u32,
        size: u32,
        size_max: u32,
        desc_address: u64,
        driver_area_address: u64,
        device_area_address: u64,
        m: &crate::memory::MemoryMap,
    ) {
        use virtio_queue::{Queue, QueueT};

        let mut device = self.device.lock().unwrap();
        let mut queue = Queue::new(size_max as u16).unwrap();
        queue.set_size(size as u16);
        queue.set_desc_table_address(Some(desc_address as u32), Some((desc_address >> 32) as u32));
        queue.set_avail_ring_address(
            Some(driver_area_address as u32),
            Some((driver_area_address >> 32) as u32),
        );
        queue.set_used_ring_address(
            Some(device_area_address as u32),
            Some((device_area_address >> 32) as u32),
        );
        queue.set_event_idx(false);
        queue.set_ready(true);
        assert!(queue.is_valid(m));

        device.insert(queue_selection, queue);
    }

    fn queue_set_not_ready(&self, queue_selection: u32, _m: &crate::memory::MemoryMap) {
        use virtio_queue::QueueT;
        let mut device = self.device.lock().unwrap();
        let queue = device.get_mut(&queue_selection).unwrap();
        queue.set_ready(false);
    }

    fn queue_notify(&self, queue_selection: u32, m: &crate::memory::MemoryMap) {
        use virtio_queue::{QueueOwnedT, QueueT};
        let mut device = self.device.lock().unwrap();
        let queue = device.get_mut(&queue_selection).unwrap();
        loop {
            queue.disable_notification(m).unwrap();

            while let Some(chain) = queue.iter(m).unwrap().next() {
                self.backend
                    .lock()
                    .unwrap()
                    .process_requests(queue_selection, queue, chain, m);

                if queue.needs_notification(m).unwrap() {
                    self.state.lock().unwrap().interrupt_status_used_buffer = true;
                    _ = self.irq_generator.irq_sender.try_send(
                        crate::machine::interrupts::InterruptRequest {
                            interrupt_id: self.interrupt_id + 32,
                            cpu_id: None,
                            signal: true,
                        },
                    );
                }
            }
            if !queue.enable_notification(m).unwrap() {
                break;
            }
        }
    }
}
