// SPDX-License-Identifier: Apache-2.0 or BSD-3-Clause

use core::slice;
use std::{
    convert::{TryFrom, TryInto},
    io::ErrorKind,
    mem,
    path::Path,
};

pub mod scsi;
mod virtio;

use self::{
    scsi::{CmdError, Target, TaskAttr},
    virtio::{
        virtio_scsi_config, virtio_scsi_event, Request, RequestParseError, Response, ResponseCode,
        VirtioScsiLun, CDB_SIZE, SENSE_SIZE,
    },
};

pub struct Scsi {
    targets: Vec<Box<dyn Target>>,
}

impl std::fmt::Debug for Scsi {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.debug_struct("Scsi").finish_non_exhaustive()
    }
}

impl Scsi {
    pub fn new(file: &Path, read_only: bool) -> Self {
        let mut target = crate::virtio::virtio_scsi::scsi::emulation::target::EmulatedTarget::new();
        {
            use crate::virtio::virtio_scsi::scsi::emulation::block_device::*;
            let mut dev = BlockDevice::new(FileBackend::new(
                std::fs::File::options()
                    .read(true)
                    .write(!read_only)
                    .create(false)
                    .open(file)
                    .expect("Opening image"),
            ));
            dev.set_write_protected(read_only);
            dev.set_solid_state(MediumRotationRate::NonRotating);
            target.add_lun(Box::new(dev));
        }

        Self {
            targets: vec![Box::new(target)],
        }
    }

    fn parse_target(&mut self, lun: VirtioScsiLun) -> Option<(&mut Box<dyn Target>, u16)> {
        match lun {
            VirtioScsiLun::TargetLun(target, lun) => self
                .targets
                .get_mut(usize::from(target))
                .map(|tgt| (tgt, lun)),
            VirtioScsiLun::ReportLuns => {
                // TODO: do we need to handle the REPORT LUNS well-known LUN?
                // In practice, everyone seems to just use LUN 0
                tracing::error!(
                    "Guest is trying to use the REPORT LUNS well-known LUN, which we don't \
                     support."
                );
                None
            }
        }
    }
}

impl super::VirtioBackend for Scsi {
    const ID: super::DeviceType = super::DeviceType::ScsiHost;
    const NUM_OF_QUEUES: usize = 3;

    fn process_requests(
        &mut self,
        queue_selection: u32,
        queue: &mut virtio_queue::Queue,
        desc_chain: virtio_queue::DescriptorChain<&crate::memory::MemoryMap>,
        mem: &crate::memory::MemoryMap,
    ) {
        use virtio_queue::QueueT;

        match queue_selection {
            0 => {
                // controlq
                todo!()
            }
            1 => {
                // eventq
                todo!()
            }
            2 => {
                // requestq

                let mut reader = virtio::DescriptorChainReader::new(desc_chain.clone());
                let mut writer = virtio::DescriptorChainWriter::new(desc_chain.clone());
                let mut body_writer = writer.clone();
                const RESPONSE_HEADER_SIZE: u32 = 12;
                body_writer.skip(
                    RESPONSE_HEADER_SIZE
                        + u32::try_from(SENSE_SIZE).expect("SENSE_SIZE should fit 32bit"),
                );

                let response = match Request::parse(&mut reader) {
                    Ok(r) => {
                        // tracing::debug!("request: {r:?}");
                        if let Some((target, lun)) = self.parse_target(r.lun) {
                            let output = target.execute_command(
                                lun,
                                &mut reader,
                                &mut body_writer,
                                scsi::Request {
                                    id: r.id,
                                    cdb: &r.cdb,
                                    task_attr: match r.task_attr {
                                        0 => TaskAttr::Simple,
                                        1 => TaskAttr::Ordered,
                                        2 => TaskAttr::HeadOfQueue,
                                        3 => TaskAttr::Aca,
                                        _ => {
                                            // virtio-scsi spec allows us to map any task attr to
                                            // simple, presumably including future ones
                                            tracing::error!("Unknown task attr: {}", r.task_attr);
                                            TaskAttr::Simple
                                        }
                                    },
                                    crn: r.crn,
                                    prio: r.prio,
                                },
                            );

                            match output {
                                Ok(output) => {
                                    assert!(output.sense.len() < SENSE_SIZE);

                                    Response {
                                        code: ResponseCode::Ok,
                                        status: output.status,
                                        status_qualifier: output.status_qualifier,
                                        sense: output.sense,
                                        // TODO: handle residual for data in
                                        residual: body_writer.residual(),
                                    }
                                }
                                Err(CmdError::CdbTooShort) => {
                                    // the CDB buffer is, by default, sized larger than any CDB we
                                    // support; we don't handle writes to config space (because
                                    // QEMU doesn't let us), so there's no way the guest can set it
                                    // too small
                                    unreachable!();
                                }
                                Err(CmdError::DataIn(e)) => {
                                    if e.kind() == ErrorKind::WriteZero {
                                        Response::error(ResponseCode::Overrun, 0)
                                    } else {
                                        tracing::error!(
                                            "Error writing response to guest memory: {e}"
                                        );

                                        // There's some chance the header and data in are on
                                        // different descriptors, and only the data in descriptor
                                        // is bad, so let's at least try to write an error to the
                                        // header
                                        Response::error(
                                            ResponseCode::Failure,
                                            body_writer.residual(),
                                        )
                                    }
                                }
                            }
                        } else {
                            tracing::error!("Rejecting command to LUN with bad target {:?}", r.lun);
                            Response::error(ResponseCode::BadTarget, body_writer.residual())
                        }
                    }
                    Err(RequestParseError::CouldNotReadGuestMemory(e)) => {
                        // See comment later about errors while writing to guest mem; maybe we at
                        // least got functional write descriptors, so we can
                        // report an error
                        tracing::error!("Error reading request from guest memory: {e:?}");
                        Response::error(ResponseCode::Failure, body_writer.residual())
                    }
                    Err(RequestParseError::FailedParsingLun(lun)) => {
                        tracing::error!("Unable to parse LUN: {lun:?}");
                        Response::error(ResponseCode::Failure, body_writer.residual())
                    }
                };

                if let Err(e) = response.write(&mut writer) {
                    // Alright, so something went wrong writing our response header to guest memory.
                    // The only reason this should ever happen, I think, is if the guest gave us a
                    // virtio descriptor with an invalid address.

                    // There's not a great way to recover from this - we just discovered that
                    // our only way of communicating with the guest doesn't work - so we either
                    // silently fail or crash. There isn't too much sense in crashing, IMO, as
                    // the guest could still recover by, say, installing a fixed kernel and
                    // rebooting. So let's just log an error and do nothing.
                    tracing::error!("Error writing response to guest memory: {e:?}");
                }

                if queue
                    .add_used(mem, desc_chain.head_index(), writer.max_written())
                    .is_err()
                {
                    tracing::error!("Couldn't return used descriptors to the ring");
                }
            }
            other => unreachable!("{other}"),
        }
    }

    fn config(&self, offset: u32, size: u32) -> Vec<u8> {
        let config = virtio_scsi_config {
            num_queues: 1,
            seg_max: 128 - 2,
            max_sectors: 0xFFFF,
            cmd_per_lun: 128,
            event_info_size: mem::size_of::<virtio_scsi_event>()
                .try_into()
                .expect("event info size should fit 32bit"),
            sense_size: SENSE_SIZE.try_into().expect("SENSE_SIZE should fit 32bit"),
            cdb_size: CDB_SIZE.try_into().expect("CDB_SIZE should fit 32bit"),
            max_channel: 0,
            max_target: 255,
            max_lun: u32::from((!u16::from(VirtioScsiLun::ADDRESS_METHOD_PATTERN) << 8) | 0xff),
        };

        // SAFETY: Pointer is aligned (points to start of struct), valid and we only
        // access up to the size of the struct.
        let config_slice = unsafe {
            slice::from_raw_parts(
                (&raw const config).cast::<u8>(),
                mem::size_of::<virtio_scsi_config>(),
            )
        };

        config_slice
            .iter()
            .skip(offset as usize)
            .take(size as usize)
            .cloned()
            .collect()
    }
}
