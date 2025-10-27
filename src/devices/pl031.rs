// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Emulated PL031 RTC.

use std::sync::{Arc, Mutex};

use crate::{
    devices::{DeviceOps, MemoryTxResult},
    machine::interrupts::{InterruptGenerator, Interrupts},
    memory::{Address, MemoryRegion, MemorySize, Width},
};

#[repr(C)]
#[derive(Debug, Default)]
/// Register file.
pub struct PL031Registers {
    pub match_: u32,
    pub load: u32,
    pub control: bool,
    pub mask: bool,
    pub int_status: bool,
    pub masked_int_status: bool,
}

#[derive(Debug)]
/// PL031 Device Model
pub struct PL031State {
    /// Device ID.
    pub device_id: u64,
    address: Address,
    regs: Arc<Mutex<PL031Registers>>,
    irq_generator: InterruptGenerator,
}

impl crate::devices::Device for PL031State {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn into_memory_regions(self) -> Vec<MemoryRegion> {
        let Self {
            device_id,
            address,
            regs,
            irq_generator,
        } = self;

        vec![MemoryRegion::new_io(
            MemorySize::new(0x1000).unwrap(),
            address,
            0,
            Box::new(PL031MemoryOps {
                device_id,
                regs,
                irq_generator,
            }),
        )
        .unwrap()]
    }
}

#[derive(Debug)]
struct PL031MemoryOps {
    device_id: u64,
    regs: Arc<Mutex<PL031Registers>>,
    // [ref:TODO]: Implement interrupt/alarm function
    #[allow(dead_code)]
    irq_generator: InterruptGenerator,
}

impl DeviceOps for PL031MemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, _width: Width) -> MemoryTxResult<u64> {
        use nix::time::{clock_gettime, ClockId};

        const PL031_ID: &[u8] = &[
            // Device ID
            0x31, 0x10, 0x14, 0x00, // Cell ID
            0x0d, 0xf0, 0x05, 0xb1,
        ];
        let ret = match offset {
            0x000..0x004 => Ok(clock_gettime(ClockId::CLOCK_REALTIME).unwrap().tv_sec() as u64),
            0x004..0x008 => {
                // RTCMR Match Register, RTCMR
                Ok(self.regs.lock().unwrap().match_.into())
            }
            0x008..0x00c => {
                // RW 32 0x00000000 RTCLR Load Register, RTCLR
                Ok(self.regs.lock().unwrap().load.into())
            }
            0x00c..0x010 => {
                // RW 1 0x00000000 RTCCR Control Register, RTCCR
                Ok(1)
            }
            0x010..0x014 => {
                // RW	1 0x00000000 RTCIMSC Interrupt Mask Set or Clear register, RTCIMSC
                Ok(self.regs.lock().unwrap().mask.into())
            }
            0x014..0x018 => {
                // RO 1 0x00000000 RTCRIS Raw Interrupt Status, RTCRIS
                Ok(self.regs.lock().unwrap().int_status.into())
            }
            0x018..0x01c => {
                // RO 1 0x00000000 RTCMIS Masked Interrupt Status, RTCMIS
                Ok(self.regs.lock().unwrap().masked_int_status.into())
            }
            0x01c..0x020 => {
                // WO 1 0x00000000 RTCICR Interrupt Clear Register, RTCICR
                Ok(0)
            }
            0x020..0xfdc => {
                // Reserved
                Ok(0)
            }
            0xfe0..0xfe4 => {
                // RO 8 0x31 RTCPeriphID0 Peripheral ID register bits[7:0]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xfe4..0xfe8 => {
                // RO 8 0x10 RTCPeriphID1 Peripheral ID register bits[15:8]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xfe8..0xfec => {
                // RO 8 0x04 RTCPeriphID2 Peripheral ID register bits[23:16]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xfec..0xff0 => {
                // RO 8 0x00 RTCPeriphID3 Peripheral ID register bits[31:24]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xff0..0xff4 => {
                // RO 8 0D RTCPCellID0 PrimeCell ID register bits[7:0]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xff4..0xff8 => {
                // RO 8 F0 RTCPCellID1 PrimeCell ID register bits[15:8]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xff8..0xffc => {
                // RO 8 05 RTCPCellID2 PrimeCell ID register bits[23:16]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            0xffc..0x1000 => {
                // RO 8 B1 RTCPCellID3 PrimeCell ID register bits[31:24]
                Ok(PL031_ID[(offset as usize - 0xfe0) >> 2].into())
            }
            _other => {
                panic!();
            }
        };
        ret
    }

    fn write(&self, offset: u64, value: u64, _width: Width) -> MemoryTxResult {
        match offset {
            0x000..0x004 => {}
            0x004..0x008 => {
                // RTCMR Match Register, RTCMR
                self.regs.lock().unwrap().match_ = value as u32;
            }
            0x008..0x00c => {
                // RW 32 0x00000000 RTCLR Load Register, RTCLR
                self.regs.lock().unwrap().load = value as u32;
            }
            0x00c..0x010 => {
                // RW 1 0x00000000 RTCCR Control Register, RTCCR
                self.regs.lock().unwrap().control = value & 1 > 0;
            }
            0x010..0x014 => {
                // RW	1 0x00000000 RTCIMSC Interrupt Mask Set or Clear register, RTCIMSC
                self.regs.lock().unwrap().mask = value & 1 > 0;
            }
            0x014..0x018 => {
                // RO 1 0x00000000 RTCRIS Raw Interrupt Status, RTCRIS
            }
            0x018..0x01c => {
                // RO 1 0x00000000 RTCMIS Masked Interrupt Status, RTCMIS
            }
            0x01c..0x020 => {
                // WO 1 0x00000000 RTCICR Interrupt Clear Register, RTCICR
                // TODO
            }
            0x020..0xfdc => {
                // Reserved
            }
            0xfe0..0xfe4 => {
                // RO 8 0x31 RTCPeriphID0 Peripheral ID register bits[7:0]
            }
            0xfe4..0xfe8 => {
                // RO 8 0x10 RTCPeriphID1 Peripheral ID register bits[15:8]
            }
            0xfe8..0xfec => {
                // RO 8 0x04 RTCPeriphID2 Peripheral ID register bits[23:16]
            }
            0xfec..0xff0 => {
                // RO 8 0x00 RTCPeriphID3 Peripheral ID register bits[31:24]
            }
            0xff0..0xff4 => {
                // RO 8 0D RTCPCellID0 PrimeCell ID register bits[7:0]
            }
            0xff4..0xff8 => {
                // RO 8 F0 RTCPCellID1 PrimeCell ID register bits[15:8]
            }
            0xff8..0xffc => {
                // RO 8 05 RTCPCellID2 PrimeCell ID register bits[23:16]
            }
            0xffc..0x1000 => {
                // RO 8 B1 RTCPCellID3 PrimeCell ID register bits[31:24]
            }
            _other => {
                panic!();
            }
        }
        Ok(())
    }

    #[inline(always)]
    fn supports_device_tree(&'_ self) -> Option<crate::devices::DeviceTreeOps<'_>> {
        Some(self)
    }
}

impl crate::devices::DeviceTreeExt for PL031MemoryOps {
    fn kind(&self) -> Option<crate::fdt::NodeKind> {
        Some(crate::fdt::NodeKind::Stdout("pl031".to_string()))
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
        assert_eq!(len, 0x1000);

        let pl031_node = writer.begin_node(&format!("pl031@{start:x?}"))?;
        writer.property_string_list("clock-names", vec!["apb_pclk".to_string()])?;
        writer.property_array_u32("clocks", &[ctx.phandle_clk])?;
        writer.property_array_u32("interrupts", &[0x00, 0x02, 0x04])?;
        writer.property_array_u64("reg", &[start, len])?;
        writer.property_string_list(
            "compatible",
            vec!["arm,pl031".to_string(), "arm,primecell".to_string()],
        )?;
        writer.end_node(pl031_node)?;
        Ok(())
    }
}

impl PL031State {
    pub fn new(device_id: u64, address: Address, interrupts: &Interrupts) -> Self {
        let irq_generator = interrupts.generator.clone();
        Self {
            device_id,
            address,
            irq_generator,
            regs: Default::default(),
        }
    }
}
