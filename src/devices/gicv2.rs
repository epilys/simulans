// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

#![allow(clippy::significant_drop_tightening)]

//! # ARM ® Generic Interrupt Controller Architecture version 2.0

// Questions:
//
// - When should the IRQ/FIQ signals be cleared?

use std::sync::{Arc, Mutex};

use crate::{
    get_bits,
    machine::interrupts::{FiqSignal, InterruptRequest, Interrupts, IrqSignal},
    memory::{Address, DeviceMemoryOps, MemoryRegion, MemorySize, MemoryTxResult, Width},
    set_bits, tracing,
};

#[derive(Debug, Copy, Clone)]
pub enum InterruptState {
    Inactive,
    Pending,
    Active,
    ActiveAndPending,
}

const MINIMUM_BINARY_POINT: u8 = 0x3;
const NS_ACCESS: bool = true;
const SPURIOUS_INTERRUPT: u16 = 1023;

// Helper functions
// ================
// bits(3) SGI_CpuID(integer InterruptID, cpu_id)
// // Returns the ID of a source CPU for a pending interrupt
// // with the given interruptID targeting the current
// // CPU. If there are multiple source CPUs, the one
// // chosen is IMPLEMENTATION SPECIFIC.

#[doc(alias("GIC_PriorityMask"))]
/// Returns the priority mask to be used for priority grouping as part of
/// interrupt prioritization
// NOTE: where the Security Extensions are not supported, NS_mask = '0'
fn priority_mask(mut n: u8, ns_mask: bool) -> u8 {
    // Range check for the priority mask.
    assert!((0..=7).contains(&n));
    if ns_mask {
        // Mask generation for a secure GIC access.
        n -= 1;
    }
    // CHECK:
    if n < MINIMUM_BINARY_POINT {
        // Saturate n on the minimum value supported; range 0-3
        n = MINIMUM_BINARY_POINT; // NOTE: min. value is the SECURE value where
                                  // supported
    }
    (0b1111111100000000_u32 >> (7 - n)) as u8
}

/// Returns pending interrupts, masked by distributor enables but not cpu if
/// enables
fn update_exception_state(gicc: &Gicc, gicd: &Gicd, cpu_id: u8) -> (bool, bool) {
    let sbp = gicc.bpr; // Secure version of this register.
    let nsbp = gicc.abpr;
    let mut next_int = false;
    let mut next_grp0 = false;
    // Establish the ID of the highest pending interrupt on the this CPU interface.
    let int_id = highest_priority_pending_interrupt(gicd, cpu_id);

    if priority_is_higher(gicd.priority(int_id, cpu_id), gicc.pmr as u8)
        && gicd.is_pending(int_id, cpu_id)
    {
        let smsk = priority_mask(sbp as u8, false);

        let nsmsk = if gicc.cbpr() {
            smsk
        } else {
            priority_mask(nsbp as u8, true)
        };
        // Highest pending interrupt is secure
        //// and secure interrupts are enabled
        if gicd.is_grp0_int(int_id, cpu_id) && gicd.group0_enabled() {
            if !gicd.any_active_interrupts(cpu_id)
                || priority_is_higher(gicd.priority(int_id, cpu_id), gicc.pmr as u8 & smsk)
            {
                next_int = true;
                next_grp0 = true;
            }
        } else {
            // Highest pending interrupt is non-secure and non-secure interrupts are enabled
            if (!gicd.is_grp0_int(int_id, cpu_id))
                && gicd.group1_enabled()
                && !gicd.any_active_interrupts(cpu_id)
                || priority_is_higher(gicd.priority(int_id, cpu_id), gicc.pmr as u8 & nsmsk)
            {
                next_int = true;
                next_grp0 = false;
            }
        }
    }

    (next_int, next_grp0)
}

#[doc(alias("PriorityIsHigher"))]
/// Return `true` if the first argument of the function has a higher priority
/// than the second argument.
fn priority_is_higher(pr1: u8, pr2: u8) -> bool {
    // Lower number represents higher priority.
    pr1 < pr2
}

// Returns the ID of the highest priority interrupt that is pending and enabled.
// Otherwise, returns 1023 (i.e. a spurious interrupt)
//
// In implementations where interrupts are masked by the distributor group
// enable bits AFTER prioritisation (i.e. IGNORE_GROUP_ENABLE is TRUE), this
// function may return the ID of a pending interrupt in a disabled group even
// though there is a (lower priority) pending interrupt that is fully enabled
// (i.e. enabled in GICD_IENABLER and the appropriate group enable bit is '1' in
// GICD_CTLR). This is a helper function only and does not explain the full
// effect of GICC_HPPIR. The value returned by a read of GICC_HPPIR is explained
// in the pseudocode provided with the register description.
#[doc(alias("HighestPriorityPendingInterrupt"))]
fn highest_priority_pending_interrupt(gicd: &Gicd, cpu_id: u8) -> u16 {
    const IGNORE_GROUP_ENABLE: bool = false;

    // Work out how many interrupts are supported
    let num_interrupts = 32 * (get_bits!(gicd.typer, off = 0, len = 5) as u16 + 1);
    // Set initial ID to be spurious
    let mut hppi = SPURIOUS_INTERRUPT;
    for int_id in 0..num_interrupts {
        let group_enabled = (gicd.is_grp0_int(int_id, cpu_id) && (gicd.group0_enabled()))
            || (!gicd.is_grp0_int(int_id, cpu_id) && (gicd.group1_enabled()));

        if gicd.is_pending(int_id, cpu_id)
            && gicd.is_enabled(int_id, cpu_id)
            && (group_enabled || IGNORE_GROUP_ENABLE)
            && priority_is_higher(gicd.priority(int_id, cpu_id), gicd.priority(hppi, cpu_id))
        {
            hppi = int_id;
        }
    }
    hppi
}

#[derive(Debug)]
pub struct GicV2 {
    /// Device ID.
    device_id: u64,
    dist: Address,
    cpu_if: Address,
    state: Arc<Mutex<State>>,
}

impl GicV2 {
    pub fn new(
        device_id: u64,
        dist: Address,
        cpu_if: Address,
        interrupts: &mut Interrupts,
    ) -> Self {
        if (dist < cpu_if && dist + 0x10000_u64 > cpu_if)
            || (cpu_if < dist && cpu_if + 0x10000_u64 > dist)
        {
            panic!(
                "GicV2 distributor memory at {dist} overlaps with CPU interface memory at \
                 {cpu_if} (each is sized  0x10000 bytes)"
            );
        }
        let fiq_signal = interrupts.fiq_signal();
        let irq_signal = interrupts.irq_signal();
        let state = Arc::new(Mutex::new(State::new()));
        let handler = Box::new({
            let state = Arc::clone(&state);
            move |irq: InterruptRequest| {
                tracing::event!(
                    target: tracing::TraceItem::GicV2.as_str(),
                    tracing::Level::TRACE,
                    kind = "interrupt request",
                    req = ?irq
                );
                let mut state_lck = state.lock().unwrap();
                if let Some(cpu_id) = irq.cpu_id {
                    state_lck.gicd.set_pending(irq.interrupt_id, cpu_id, true);
                } else {
                    for cpu_id in 0..8 {
                        state_lck.gicd.set_pending(irq.interrupt_id, cpu_id, true);
                    }
                }
                state_lck.generate_exceptions(&fiq_signal, &irq_signal);
            }
        });
        interrupts.subscribe(device_id, handler);

        Self {
            device_id,
            dist,
            cpu_if,
            state,
        }
    }
}

impl crate::devices::Device for GicV2 {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn into_memory_regions(self) -> Vec<MemoryRegion> {
        // [ref:multiprocessing]: each cpu should get a map of its own gicc registers
        let Self {
            device_id,
            dist,
            cpu_if,
            state,
        } = self;
        vec![
            MemoryRegion::new_io(
                MemorySize::new(0x10000).unwrap(),
                dist,
                Box::new(GicV2DistMemoryOps {
                    cpu_id: 0,
                    device_id,
                    state: state.clone(),
                }),
            )
            .unwrap(),
            MemoryRegion::new_io(
                MemorySize::new(0x10000).unwrap(),
                cpu_if,
                Box::new(GicV2CPUMemoryOps {
                    cpu_id: 0,
                    device_id,
                    state,
                }),
            )
            .unwrap(),
        ]
    }
}

#[derive(Debug)]
struct GicV2DistMemoryOps {
    cpu_id: u8,
    device_id: u64,
    state: Arc<Mutex<State>>,
}

// Note: The GICD_IPRIORITYR, GICD_ITARGETSR, GICD_CPENDSGIR, ad GICD_SPENDSGIR
// registers support byte accesses
impl DeviceMemoryOps for GicV2DistMemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> MemoryTxResult<u64> {
        let state = self.state.lock().unwrap();
        let gicd = &state.gicd;
        let field: &'static str;
        let value = match offset {
            (0x000..0x004) => {
                // GICD_CTLR RW 0x00000000 Distributor Control Register
                field = "GICD_CTLR";
                gicd.ctlr
            }
            (0x004..0x008) => {
                // GICD_TYPER RO IMPLEMENTATION DEFINED Interrupt Controller Type Register
                field = "GICD_TYPER";
                gicd.typer
            }
            (0x008..0x00c) => {
                // GICD_IIDR RO IMPLEMENTATION DEFINED Distributor Implementer Identification
                // Register
                field = "GICD_IIDR";
                gicd.iidr
            }
            (0x00C..0x020) => {
                field = "Reserved";
                0
            }
            (0x020..0x040) => {
                field = "IMPLEMENTATION DEFINED registers";
                0
            }
            (0x040..0x080) => {
                field = "Reserved";
                0
            }
            (0x080..0x084) => {
                // GICD_IGROUPRn b RW IMPLEMENTATION DEFINED c Interrupt Group Registers
                field = "GICD_IGROUPR";
                let idx = (offset - 0x080) / 0x4;
                if idx == 0 {
                    gicd.igroupr0[self.cpu_id as usize]
                } else {
                    gicd.igroupr[idx as usize]
                }
            }
            (0x084..0x100) => {
                // x00000000
                field = "GICD_IGROUPR";
                0
            }
            (0x100..0x180) => {
                // GICD_ISENABLER RW IMPLEMENTATION DEFINED Interrupt Set-Enable Registers
                field = "GICD_ISENABLER";
                let idx = (offset - 0x100) / 0x4;
                if idx == 0 {
                    gicd.enabled_interrupts0[self.cpu_id as usize]
                } else {
                    gicd.enabled_interrupts[idx as usize]
                }
            }
            (0x180..0x200) => {
                // GICD_ICENABLER RW IMPLEMENTATION DEFINED Interrupt Clear-Enable Registers
                field = "GICD_ICENABLER";
                let idx = (offset - 0x180) / 0x4;
                if idx == 0 {
                    gicd.enabled_interrupts0[self.cpu_id as usize]
                } else {
                    gicd.enabled_interrupts[idx as usize]
                }
            }
            (0x200..0x280) => {
                // GICD_ISPENDR RW 0x00000000 Interrupt Set-Pending Registers
                field = "GICD_ISPENDR";
                let idx = (offset - 0x200) / 0x4;
                if idx == 0 {
                    gicd.pending_interrupts0[self.cpu_id as usize]
                } else {
                    gicd.pending_interrupts[idx as usize]
                }
            }
            (0x280..0x300) => {
                // GICD_ICPENDR RW 0x00000000 Interrupt Clear-Pending Registers
                field = "GICD_ICPENDR";
                let idx = (offset - 0x280) / 0x4;
                if idx == 0 {
                    gicd.pending_interrupts0[self.cpu_id as usize]
                } else {
                    gicd.pending_interrupts[idx as usize]
                }
            }
            (0x300..0x380) => {
                // GICD_ISACTIVER RW 0x00000000 GICv2 Interrupt Set-Active Registers
                field = "GICD_ISACTIVER";
                let idx = (offset - 0x300) / 0x4;
                if idx == 0 {
                    gicd.active_interrupts0[self.cpu_id as usize]
                } else {
                    gicd.active_interrupts[idx as usize]
                }
            }
            (0x380..0x400) => {
                // GICD_ICACTIVER RW 0x00000000 Interrupt Clear-Active Registers
                field = "GICD_ICACTIVER";
                let idx = (offset - 0x380) / 0x4;
                if idx == 0 {
                    gicd.active_interrupts0[self.cpu_id as usize]
                } else {
                    gicd.active_interrupts[idx as usize]
                }
            }
            (0x400..0x7FC) => {
                // GICD_IPRIORITYR RW 0x00000000 Interrupt Priority Registers
                field = "GICD_IPRIORITYR";
                let idx = (offset - 0x400) / 0x4;
                let byte_offset = (offset - 0x400) % 0x4;
                if byte_offset != 0 {
                    gicd.priority((offset - 0x400) as u16, self.cpu_id).into()
                } else if idx == 0 {
                    gicd.ipriorityr0[self.cpu_id as usize]
                } else {
                    gicd.ipriorityr[idx as usize]
                }
            }
            (0x7FC..0x800) => {
                field = "Reserved";
                0
            }
            (0x800..0x8FC) => {
                // GICD_ITARGETSR RO f IMPLEMENTATION DEFINED Interrupt Processor Targets
                // Registers
                field = "GICD_ITARGETSR";
                let idx = (offset - 0x800) / 0x4;
                let byte_offset = (offset - 0x800) % 0x4;
                let value = if idx < 8 {
                    // GICD_ITARGETSR0 to GICD_ITARGETSR7 are read-only, and each field returns a
                    // value that corresponds only to the processor reading the register.
                    (1 << self.cpu_id) as u32
                } else {
                    gicd.itargetsr[idx as usize]
                };
                if byte_offset != 0 {
                    u32::from(value.to_le_bytes()[byte_offset as usize])
                } else {
                    value
                }
            }
            (0xBFC..0xC00) => {
                field = "Reserved";
                0
            }
            (0xC00..0xD00) => {
                // GICD_ICFGR RW IMPLEMENTATION DEFINED Interrupt Configuration Registers
                field = "GICD_ICFGR";
                let idx = (offset - 0xc00) / 0x4;
                if idx == 1 {
                    gicd.icfgr1[self.cpu_id as usize]
                } else {
                    gicd.icfgr[idx as usize]
                }
            }
            (0xD00..0xE00) => {
                field = "IMPLEMENTATION DEFINED registers";
                0
            }
            (0xE00..0xF00) => {
                // GICD_NSACR RW 0x00000000 Non-secure Access Control Registers, optional
                field = "GICD_NSACR";
                0
            }
            (0xF00..0xF04) => {
                // GICD_SGIR WO - Software Generated Interrupt Register
                field = "GICD_SGIR";
                gicd.sgir
            }
            (0xF04..0xF10) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0xF10..0xF20) => {
                // GICD_CPENDSGIR RW 0x00000000 SGI Clear-Pending Registers
                field = "GICD_CPENDSGIR";
                0
            }
            (0xF20..0xF30) => {
                // GICD_SPENDSGIR RW 0x00000000 SGI Set-Pending Registers
                field = "GICD_SPENDSGIR";
                0
            }
            (0xF30..0xFD0) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0xFD0..0x1000) => {
                // - RO IMPLEMENTATION DEFINED Identification registers on page 4-119
                field = "IMPLEMENTATION DEFINED Identification registers";
                0
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
                0
            }
        }
        .into();

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            cpu_id = self.cpu_id,
            ?width,
            kind = "distributor read",
            offset = ?tracing::Hex(offset),
            field,
            value = ?tracing::BinaryHex(value),
        );

        Ok(value)
    }

    fn write(&self, offset: u64, value: u64, width: Width) -> MemoryTxResult {
        let value = value as u32;

        let mut state = self.state.lock().unwrap();
        let gicd = &mut state.gicd;
        let field: &'static str;
        match offset {
            (0x000..0x004) => {
                // GICD_CTLR RW 0x00000000 Distributor Control Register
                field = "GICD_CTLR";
                gicd.ctlr = value;
            }
            (0x004..0x008) => {
                // GICD_TYPER RO IMPLEMENTATION DEFINED Interrupt Controller Type Register
                field = "GICD_TYPER";
            }
            (0x008..0x00c) => {
                // GICD_IIDR RO IMPLEMENTATION DEFINED Distributor Implementer Identification
                // Register
                field = "GICD_IIDR";
            }
            (0x00C..0x020) => {
                // Reserved
                field = "Reserved";
            }
            (0x020..0x040) => {
                field = "IMPLEMENTATION DEFINED registers";
            }
            (0x040..0x080) => {
                // Reserved
                field = "Reserved";
            }
            (0x080..0x084) => {
                // GICD_IGROUPR b RW IMPLEMENTATION DEFINED c Interrupt Group Registers
                field = "GICD_IGROUPR";
                let idx = (offset - 0x080) / 0x4;
                if idx == 0 {
                    gicd.igroupr0[self.cpu_id as usize] = value;
                } else {
                    gicd.igroupr[idx as usize] = value;
                }
            }
            (0x084..0x100) => {
                field = "GICD_IGROUPR";
            }
            (0x100..0x180) => {
                // GICD_ISENABLER RW IMPLEMENTATION DEFINED Interrupt Set-Enable Registers
                field = "GICD_ISENABLER";
                let idx = (offset - 0x100) / 4;
                gicd.write_isenabler(idx as usize, value, self.cpu_id);
            }
            (0x180..0x200) => {
                // GICD_ICENABLER RW IMPLEMENTATION DEFINED Interrupt Clear-Enable Registers
                field = "GICD_ICENABLER";
                let idx = (offset - 0x180) / 0x4;
                gicd.write_icenabler(idx as usize, value, self.cpu_id);
            }
            (0x200..0x280) => {
                // GICD_ISPENDR RW 0x00000000 Interrupt Set-Pending Registers
                field = "GICD_ISPENDR";
                let idx = (offset - 0x200) / 0x4;
                gicd.write_ispendr(idx as usize, value, self.cpu_id);
            }
            (0x280..0x300) => {
                // GICD_ICPENDR RW 0x00000000 Interrupt Clear-Pending Registers
                field = "GICD_ICPENDR";
                let idx = (offset - 0x280) / 0x4;
                gicd.write_icpendr(idx as usize, value, self.cpu_id);
            }
            (0x300..0x380) => {
                // GICD_ISACTIVER d RW 0x00000000 GICv2 Interrupt Set-Active Registers
                field = "GICD_ISACTIVER";
                let idx = (offset - 0x300) / 0x4;
                gicd.write_isactiver(idx as usize, value, self.cpu_id);
            }
            (0x380..0x400) => {
                // GICD_ICACTIVER e RW 0x00000000 Interrupt Clear-Active Registers
                field = "GICD_ICACTIVER";
                let idx = (offset - 0x380) / 0x4;
                gicd.write_icactiver(idx as usize, value, self.cpu_id);
            }
            (0x400..0x7FC) => {
                // GICD_IPRIORITYR RW 0x00000000 Interrupt Priority Registers
                field = "GICD_IPRIORITYR";
                let idx = (offset - 0x400) / 0x4;
                let byte_offset = (offset - 0x400) % 0x4;
                if byte_offset != 0 {
                    gicd.write_priority((offset - 0x400) as u16, self.cpu_id, value as u8);
                } else if idx == 0 {
                    gicd.ipriorityr0[self.cpu_id as usize] = value;
                } else {
                    gicd.ipriorityr[idx as usize] = value;
                }
            }
            (0x7FC..0x800) => {
                // Reserved
                field = "Reserved";
            }
            (0x800..0xBFC) => {
                // GICD_ITARGETSR RO f IMPLEMENTATION DEFINED Interrupt Processor Targets
                // Registers
                field = "GICD_ITARGETSR";
                let idx = (offset - 0x800) / 0x4;
                let byte_offset = (offset - 0x800) % 0x4;
                if idx < 8 {
                    // GICD_ITARGETSR0 to GICD_ITARGETSR7 are read-only
                } else if byte_offset != 0 {
                    gicd.write_itargets((offset - 0x800) as u16, value as u8);
                } else {
                    gicd.itargetsr[idx as usize] = value;
                }
            }
            (0xBFC..0xC00) => {
                // Reserved
                field = "Reserved";
            }
            (0xC00..0xD00) => {
                // GICD_ICFGR RW IMPLEMENTATION DEFINED Interrupt Configuration Registers
                field = "GICD_ICFGR";
                let idx = (offset - 0xc00) / 0x4;
                if idx == 1 {
                    gicd.icfgr1[self.cpu_id as usize] = value;
                } else {
                    gicd.icfgr[idx as usize] = value;
                }
            }
            (0xD00..0xE00) => {
                field = "IMPLEMENTATION DEFINED registers";
            }
            (0xE00..0xF00) => {
                // GICD_NSACR e RW 0x00000000 Non-secure Access Control Registers, optional
                field = "GICD_NSACR";
            }
            (0xF00..0xF04) => {
                // GICD_SGIR WO - Software Generated Interrupt Register
                field = "GICD_SGIR";
                gicd.sgir = value;
            }
            (0xF04..0xF10) => {
                // Reserved
                field = "Reserved";
            }
            (0xF10..0xF20) => {
                // GICD_CPENDSGIR e RW 0x00000000 SGI Clear-Pending Registers
                field = "GICD_CPENDSGIR";
            }
            (0xF20..0xF30) => {
                // GICD_SPENDSGIR e RW 0x00000000 SGI Set-Pending Registers
                field = "GICD_SPENDSGIR";
            }
            (0xF30..0xFD0) => {
                // Reserved
                field = "Reserved";
            }
            (0xFD0..0x1000) => {
                // - RO IMPLEMENTATION DEFINED Identification registers on page 4-119
                field = "IMPLEMENTATION DEFINED Identification registers";
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
            }
        }

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            cpu_id = self.cpu_id,
            ?width,
            kind = "distributor write",
            offset = ?tracing::Hex(offset),
            field,
            value = ?tracing::BinaryHex(value),
        );
        Ok(())
    }
}

#[derive(Debug)]
struct GicV2CPUMemoryOps {
    device_id: u64,
    cpu_id: u8,
    state: Arc<Mutex<State>>,
}

impl DeviceMemoryOps for GicV2CPUMemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> MemoryTxResult<u64> {
        let mut state = self.state.lock().unwrap();
        let State {
            ref giccs,
            ref mut gicd,
        } = *state;
        let gicc = &giccs[self.cpu_id as usize];
        let field: &'static str;
        let value = match offset {
            (0x0000..0x0004) => {
                // GICC_CTLR RW 0x00000000 CPU Interface Control Register
                field = "GICC_CTLR";
                gicc.ctlr
            }
            (0x0004..0x0008) => {
                // GICC_PMR RW 0x00000000 Interrupt Priority Mask Register
                field = "GICC_PMR";
                gicc.pmr
            }
            (0x0008..0x000c) => {
                // GICC_BPR RW 0x0000000x a Binary Point Register
                field = "GICC_BPR";
                gicc.bpr
            }
            (0x000C..0x0010) => {
                // GICC_IAR RO 0x000003FF Interrupt Acknowledge Register
                field = "GICC_IAR";
                gicc.read_iar(gicd, self.cpu_id)
            }
            (0x0010..0x0014) => {
                // GICC_EOIR WO - End of Interrupt Register
                field = "GICC_EOIR";
                0
            }
            (0x0014..0x0018) => {
                // GICC_RPR RO 0x000000FF Running Priority Register
                field = "GICC_RPR";
                gicc.rpr
            }
            (0x0018..0x001c) => {
                // GICC_HPPIR RO 0x000003FF Highest Priority Pending Interrupt Register
                field = "GICC_HPPIR";
                gicc.hppir
            }
            (0x001C..0x0020) => {
                // GICC_ABPR b RW 0x0000000xa Aliased Binary Point Register
                field = "GICC_ABPR";
                gicc.abpr
            }
            (0x0020..0x0024) => {
                // GICC_AIAR RO 0x000003FF Aliased Interrupt Acknowledge Register
                field = "GICC_AIAR";
                gicc.read_iar(gicd, self.cpu_id)
            }
            (0x0024..0x0028) => {
                // GICC_AEOIR WO - Aliased End of Interrupt Register
                field = "GICC_AEOIR";
                0
            }
            (0x0028..0x002c) => {
                // GICC_AHPPIR RO 0x000003FF Aliased Highest Priority Pending Interrupt Register
                field = "GICC_AHPPIR";
                gicc.ahppir
            }
            (0x002C..0x0040) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0x0040..0x00D0) => {
                // IMPLEMENTATION DEFINED registers
                field = "IMPLEMENTATION DEFINED registers";
                0
            }
            (0x00D0..0x00E0) => {
                // GICC_APR RW 0x00000000 Active Priorities Registers
                field = "GICC_APR";
                // TODO
                0
            }
            (0x00E0..0x00ED) => {
                // GICC_NSAPR RW 0x00000000 Non-secure Active Priorities Registers
                field = "GICC_NSAPR";
                // TODO
                0
            }
            (0x00ED..0x00FC) => {
                // Reserved
                field = "Reserved";
                0
            }
            (0x00FC..0x0100) => {
                // GICC_IIDR RO IMPLEMENTATION DEFINED CPU Interface Identification Register
                field = "GICC_IIDR";
                gicc.iidr
            }
            (0x1000..0x1004) => {
                // GICC_DIR WO - Deactivate Interrupt Register
                field = "GICC_DIR";
                gicc.dir
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
                0
            }
        }
        .into();

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            cpu_id = self.cpu_id,
            kind = "CPU interface read",
            offset = ?tracing::Hex(offset),
            ?width,
            field,
            value = ?tracing::BinaryHex(value)
        );

        Ok(value)
    }

    fn write(&self, offset: u64, value: u64, width: Width) -> MemoryTxResult {
        let value = value as u32;

        let mut state = self.state.lock().unwrap();
        let gicc = &mut state.giccs[self.cpu_id as usize];
        let field: &'static str;
        match offset {
            (0x0000..0x0004) => {
                // GICC_CTLR RW 0x00000000 CPU Interface Control Register
                field = "GICC_CTLR";
                gicc.ctlr = value;
                tracing::event!(
                    target: tracing::TraceItem::GicV2.as_str(),
                    tracing::Level::TRACE,
                    cpu_id = self.cpu_id,
                    kind = "GICC_CTLR change",
                    EnableGrp0 = ?gicc.group0_enabled(),
                    EnableGrp1 = ?gicc.group1_enabled(),
                    AckCtl = ?gicc.ack_ctl(),
                    FIQEn = ?gicc.fiq_en(),
                    CBPR = ?gicc.cbpr(),
                    FIQBypDisGrp0 = ?gicc.fiq_byp_dis_grp0(),
                    IRQBypDisGrp0 = ?gicc.irq_byp_dis_grp0(),
                    FIQBypDisGrp1 = ?gicc.fiq_byp_dis_grp1(),
                    IRQBypDisGrp1 = ?gicc.irq_byp_dis_grp1(),
                );
            }
            (0x0004..0x0008) => {
                // GICC_PMR RW 0x00000000 Interrupt Priority Mask Register
                field = "GICC_PMR";
                gicc.pmr = value;
            }
            (0x0008..0x000c) => {
                // GICC_BPR RW 0x0000000x a Binary Point Register
                field = "GICC_BPR";
                gicc.bpr = value;
            }
            (0x000C..0x0010) => {
                // GICC_IAR RO 0x000003FF Interrupt Acknowledge Register
                field = "GICC_IAR";
            }
            (0x0010..0x0014) => {
                // GICC_EOIR WO - End of Interrupt Register
                field = "GICC_EOIR";
                gicc.eoir = value;
            }
            (0x0014..0x0018) => {
                // GICC_RPR RO 0x000000FF Running Priority Register
                field = "GICC_RPR";
            }
            (0x0018..0x001c) => {
                // GICC_HPPIR RO 0x000003FF Highest Priority Pending Interrupt Register
                field = "GICC_HPPIR";
            }
            (0x001C..0x0020) => {
                // GICC_ABPR b RW 0x0000000xa Aliased Binary Point Register
                field = "GICC_ABPR";
                gicc.abpr = value;
            }
            (0x0020..0x0024) => {
                // GICC_AIAR RO 0x000003FF Aliased Interrupt Acknowledge Register
                field = "GICC_AIAR";
            }
            (0x0024..0x0028) => {
                // GICC_AEOIR WO - Aliased End of Interrupt Register
                field = "GICC_AEOIR";
                gicc.aeoir = value;
            }
            (0x0028..0x002c) => {
                // GICC_AHPPIR RO 0x000003FF Aliased Highest Priority Pending Interrupt Register
                field = "GICC_AHPPIR";
            }
            (0x002C..0x0040) => {
                field = "Reserved";
            }
            (0x0040..0x00D0) => {
                field = "IMPLEMENTATION DEFINED registers";
            }
            (0x00D0..0x00E0) => {
                // GICC_APR RW 0x00000000 Active Priorities Registers
                field = "GICC_APR";
                // TODO
            }
            (0x00E0..0x00ED) => {
                // GICC_NSAPR RW 0x00000000 Non-secure Active Priorities Registers
                field = "GICC_NSAPR";
                // TODO
            }
            (0x00ED..0x00FC) => {
                field = "Reserved";
            }
            (0x00FC..0x0100) => {
                // GICC_IIDR RO IMPLEMENTATION DEFINED CPU Interface Identification Register
                field = "GICC_IIDR";
            }
            (0x1000..0x1004) => {
                // GICC_DIR WO - Deactivate Interrupt Register
                field = "GICC_DIR";
                gicc.dir = value;
            }
            _ => {
                // Invalid offset
                field = "Invalid offset";
            }
        }

        tracing::event!(
            target: tracing::TraceItem::GicV2.as_str(),
            tracing::Level::TRACE,
            cpu_id = self.cpu_id,
            kind = "CPU interface write",
            offset = ?tracing::Hex(offset),
            ?width,
            field,
            value = ?tracing::BinaryHex(value),
        );
        Ok(())
    }
}

#[derive(Debug)]
pub struct Gicd {
    /// Distributor Control Register
    pub ctlr: u32,
    /// Interrupt Controller Type Register
    pub typer: u32,
    /// Distributor Implementer Identification Register.
    pub iidr: u32,
    _reserved_0: [u32; 0x1D],
    /// Interrupt Group Registers
    pub igroupr: [u32; 32],
    /// `GICD_IGROUPR0` is banked for each processor
    pub igroupr0: [u32; 8],
    /// Enabled interrupts, set and cleared by writing to Interrupt Set-Enable
    /// Registers & Interrupt Clear-Enable Registers.
    pub enabled_interrupts: [u32; 32],
    /// Pending interrupts, set and cleared by writing to Interrupt Set-Pending
    /// Registers & Interrupt Clear-Pending Registers.
    pub pending_interrupts: [u32; 32],
    /// Active interrupts, set and cleared by writing to Interrupt Set-Active
    /// Registers & Interrupt Clear-Active Registers.
    pub active_interrupts: [u32; 32],
    /// `GICD_ISENABLER0` is banked for each processor, for interrupts 0-31.
    pub enabled_interrupts0: [u32; 8],
    pub active_interrupts0: [u32; 8],
    pub pending_interrupts0: [u32; 8],
    /// Interrupt Priority Registers.
    pub ipriorityr: [u32; 0x100],
    pub ipriorityr0: [u32; 8],
    /// Interrupt Processor Targets Registers.
    pub itargetsr: [u32; 0x100],
    /// Interrupt Configuration Registers.
    pub icfgr: [u32; 0x40],
    /// Banked `GICD_ICFGR1` for each processor
    pub icfgr1: [u32; 8],
    _reserved_1: [u32; 0x80],
    /// Software Generated Interrupt Register.
    pub sgir: u32,
}

impl Gicd {
    pub const fn new() -> Self {
        Self {
            ctlr: 0,
            typer: 0b11111,
            iidr: 0,
            _reserved_0: [0; 0x1D],
            igroupr: [0; 32],
            igroupr0: [0; 8],
            enabled_interrupts: [0; 32],
            pending_interrupts: [0; 32],
            active_interrupts: [0; 32],
            // Banked
            enabled_interrupts0: [0; 8],
            pending_interrupts0: [0; 8],
            active_interrupts0: [0; 8],
            ipriorityr: [0; 0x100],
            ipriorityr0: [0; 8],
            itargetsr: [0; 0x100],
            icfgr: [0; 0x40],
            icfgr1: [0; 8],
            _reserved_1: [0; 0x80],
            sgir: 0,
        }
    }

    const fn cpu_count(&self) -> u8 {
        get_bits!(self.typer, off = 5, len = 2) as u8 + 1
    }

    #[doc(alias("AnyActiveInterrupts"))]
    /// Return `true` if any interrupt is in the active state
    pub fn any_active_interrupts(&self, cpu_id: u8) -> bool {
        self.active_interrupts.iter().any(|b| *b > 0)
            || self.active_interrupts0[cpu_id as usize] > 0
    }

    pub const fn interrupt_state(&self, interrupt_id: u16, cpu_id: u8) -> InterruptState {
        assert!(interrupt_id < 1024);
        let enabled = self.is_enabled(interrupt_id, cpu_id);
        let active = self.is_active(interrupt_id, cpu_id);
        let pending = self.is_pending(interrupt_id, cpu_id);
        if !enabled {
            InterruptState::Inactive
        } else if active && pending {
            InterruptState::ActiveAndPending
        } else if active {
            InterruptState::Active
        } else if pending {
            InterruptState::Pending
        } else {
            InterruptState::Inactive
        }
    }

    // boolean IsEnabled(integer InterruptID, cpu_id)
    // // Returns TRUE if the interrupt specified by the
    // // argument InterruptID is enabled in the associated
    // // GICD_ISENABLERn or GICD_ICENABLERn register.
    pub const fn is_enabled(&self, interrupt_id: u16, cpu_id: u8) -> bool {
        assert!(interrupt_id < 1024);
        let idx = interrupt_id / 32;
        let bit = interrupt_id % 32;
        if idx == 0 {
            assert!(interrupt_id < 32);
            get_bits!(
                self.enabled_interrupts0[cpu_id as usize],
                off = bit,
                len = 1
            ) == 1
        } else {
            get_bits!(self.enabled_interrupts[idx as usize], off = bit, len = 1) == 1
        }
    }

    /// Returns `true` if the interrupt specified by argument `interrupt_id`
    // is pending for the CPU specified by argument `cpu_id`
    pub const fn is_pending(&self, interrupt_id: u16, cpu_id: u8) -> bool {
        assert!(interrupt_id < 1024);
        let idx = interrupt_id / 32;
        let bit = interrupt_id % 32;

        let target_cpus = self.read_itargets_for_id(interrupt_id, cpu_id);
        let pending = if idx == 0 {
            assert!(interrupt_id < 32);
            get_bits!(
                self.pending_interrupts0[cpu_id as usize],
                off = bit,
                len = 1
            ) == 1
        } else {
            get_bits!(self.pending_interrupts[idx as usize], off = bit, len = 1) == 1
        };
        get_bits!(target_cpus, off = cpu_id, len = 1) == 1 && pending
    }

    pub const fn is_active(&self, interrupt_id: u16, cpu_id: u8) -> bool {
        assert!(interrupt_id < 1024);
        let idx = interrupt_id / 32;
        let bit = interrupt_id % 32;
        if idx == 0 {
            assert!(interrupt_id < 32);
            get_bits!(self.active_interrupts0[cpu_id as usize], off = bit, len = 1) == 1
        } else {
            get_bits!(self.active_interrupts[idx as usize], off = bit, len = 1) == 1
        }
    }

    pub const fn set_active(&mut self, interrupt_id: u16, cpu_id: u8) {
        assert!(interrupt_id < 1024);
        let idx = interrupt_id / 32;
        let bit = interrupt_id % 32;

        if idx == 0 {
            assert!(interrupt_id < 32);
            self.active_interrupts0[cpu_id as usize] = set_bits!(
                self.active_interrupts0[cpu_id as usize],
                off = bit,
                len = 1,
                val = 1
            );
        } else {
            self.active_interrupts[idx as usize] = set_bits!(
                self.active_interrupts[idx as usize],
                off = bit,
                len = 1,
                val = 1
            );
        }
    }

    pub const fn set_pending(&mut self, interrupt_id: u16, cpu_id: u8, value: bool) {
        assert!(interrupt_id < 1024);
        let idx = interrupt_id / 32;
        let bit = interrupt_id % 32;

        if idx == 0 {
            assert!(interrupt_id < 32);
            self.pending_interrupts0[cpu_id as usize] = set_bits!(
                self.pending_interrupts0[cpu_id as usize],
                off = bit,
                len = 1,
                val = value as u32
            );
        } else {
            self.pending_interrupts[idx as usize] = set_bits!(
                self.pending_interrupts[idx as usize],
                off = bit,
                len = 1,
                val = value as u32
            );
        }
    }

    /// Returns the 8-bit priority field from the `GICD_IPRIORITYR` associated
    /// with the argument `interrupt_id`.
    #[doc(alias("ReadGICD_IPRIORITYR"))]
    pub const fn priority(&self, interrupt_id: u16, cpu_id: u8) -> u8 {
        if interrupt_id == SPURIOUS_INTERRUPT {
            return u8::MAX;
        }
        // banked
        let idx = interrupt_id / 4;
        let byte_offset = interrupt_id % 4;
        if idx == 0 {
            assert!(interrupt_id < 32);
            self.ipriorityr0[cpu_id as usize].to_le_bytes()[byte_offset as usize]
        } else {
            self.ipriorityr[idx as usize].to_le_bytes()[byte_offset as usize]
        }
    }

    #[doc(alias("WriteGICD_IPRIORITYR"))]
    /// Updates the priority field in the `GICD_IPRIORITYR` associated with the
    /// argument `interrupt_id` with the 8-bit value.
    pub const fn write_priority(&mut self, interrupt_id: u16, cpu_id: u8, value: u8) {
        // banked
        let idx = interrupt_id / 4;
        let byte_offset = interrupt_id % 4;
        if idx == 0 {
            assert!(interrupt_id < 32);
            let mut tmp = self.ipriorityr0[cpu_id as usize].to_le_bytes();
            tmp[byte_offset as usize] = value;
            self.ipriorityr0[cpu_id as usize] = u32::from_le_bytes(tmp);
        } else {
            let mut tmp = self.ipriorityr[idx as usize].to_le_bytes();
            tmp[byte_offset as usize] = value;
            self.ipriorityr[idx as usize] = u32::from_le_bytes(tmp);
        }
    }

    const fn write_itargets(&mut self, interrupt_id: u16, value: u8) {
        // banked
        let idx = interrupt_id / 4;
        let byte_offset = interrupt_id % 4;
        assert!(idx > 0);
        let mut tmp = self.itargetsr[idx as usize].to_le_bytes();
        tmp[byte_offset as usize] = value;
        self.itargetsr[idx as usize] = u32::from_le_bytes(tmp);
    }

    pub const fn group0_enabled(&self) -> bool {
        self.ctlr & 1 > 0
    }

    pub const fn group1_enabled(&self) -> bool {
        self.ctlr & 2 > 0
    }

    /// Returns `true` if the field in the `GICD_IGROUPRn` register associated
    /// with the argument `interrupt_id` is set to 0, indicating that the
    /// interrupt is configured as a Group 0 interrupt.
    #[doc(alias("IsGrp0Int"))]
    pub const fn is_grp0_int(&self, interrupt_id: u16, cpu_id: u8) -> bool {
        assert!(interrupt_id < 1024);
        let idx = interrupt_id / 32;
        let bit = interrupt_id % 32;
        if idx == 0 {
            get_bits!(self.igroupr0[cpu_id as usize], off = bit, len = 1) == 0
        } else {
            get_bits!(self.igroupr[idx as usize], off = bit, len = 1) == 0
        }
    }

    /// Returns an 8-bit field specifying which CPUs should receive the
    /// interrupt specified by argument `interrupt_id`
    #[doc(alias("ReadGICD_ITARGETSR"))]
    pub const fn read_itargets_for_id(&self, interrupt_id: u16, cpu_id: u8) -> u8 {
        // banked
        let idx = interrupt_id / 4;
        let byte_offset = interrupt_id % 4;
        if idx < 8 {
            assert!(interrupt_id < 32);
            1 << cpu_id
        } else if self.cpu_count() == 1 {
            1 << cpu_id
        } else {
            self.itargetsr[idx as usize].to_le_bytes()[byte_offset as usize]
        }
    }

    pub fn write_isenabler(&mut self, idx: usize, value: u32, cpu_id: u8) {
        // Writing 1 to a Set-enable bit enables forwarding the interrupt
        if idx == 0 {
            self.enabled_interrupts0[cpu_id as usize] |= value;
        } else {
            self.enabled_interrupts[idx] |= value;
        }
    }

    pub fn write_icenabler(&mut self, idx: usize, value: u32, cpu_id: u8) {
        // Writing 1 to a Clear-enable bit disables forwarding the interrupt
        if idx == 0 {
            self.enabled_interrupts0[cpu_id as usize] &= !value;
        } else {
            self.enabled_interrupts[idx] &= !value;
        }
    }

    pub fn write_ispendr(&mut self, idx: usize, value: u32, cpu_id: u8) {
        if idx == 0 {
            self.pending_interrupts0[cpu_id as usize] |= value;
        } else {
            self.pending_interrupts[idx] |= value;
        }
    }

    pub fn write_icpendr(&mut self, idx: usize, value: u32, cpu_id: u8) {
        if idx == 0 {
            self.pending_interrupts0[cpu_id as usize] &= !value;
        } else {
            self.pending_interrupts[idx] &= !value;
        }
    }

    pub fn write_isactiver(&mut self, idx: usize, value: u32, cpu_id: u8) {
        if idx == 0 {
            self.active_interrupts0[cpu_id as usize] |= value;
        } else {
            self.active_interrupts[idx] |= value;
        }
    }

    pub fn write_icactiver(&mut self, idx: usize, value: u32, cpu_id: u8) {
        if idx == 0 {
            self.active_interrupts0[cpu_id as usize] &= !value;
        } else {
            self.active_interrupts[idx] &= !value;
        }
    }

    /// Set the active state and attempt to clear the pending state for the
    /// interrupt associated with the argument `interrupt_id`
    #[doc(alias("AcknowledgeInterrupt"))]
    fn acknowledge_interrupt(&mut self, interrupt_id: u16, cpu_id: u8) {
        self.set_active(interrupt_id, cpu_id);
        self.set_pending(interrupt_id, cpu_id, false);
    }
}

impl Default for Gicd {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct State {
    gicd: Gicd,
    giccs: [Gicc; 8],
}

impl State {
    pub fn new() -> Self {
        Self {
            gicd: Gicd::new(),
            giccs: const {
                let mut val = [const { Gicc::new(0) }; 8];
                let mut cpu_id = 1;
                while cpu_id < 8 {
                    val[cpu_id as usize].cpu_id = cpu_id;
                    cpu_id += 1;
                }
                val
            },
        }
    }

    #[doc(alias("GIC_GenerateExceptions"))]
    #[doc(alias("GenerateExceptions"))]
    fn generate_exceptions(&self, fiq_signal: &FiqSignal, irq_signal: &IrqSignal) {
        let gicd = &self.gicd;

        let cpu_count = gicd.cpu_count();

        for cpu_id in 0..cpu_count {
            let gicc = &self.giccs[cpu_id as usize];

            // Returns pending interrupts, masked by distributor enables but not cpu i/f
            // enables
            let (next_int, next_grp0) = update_exception_state(gicc, gicd, cpu_id);

            // IRQ signal to CPU
            let mut cpu_irq = false;
            // FIQ signal to CPU
            let mut cpu_fiq = false;

            if next_int {
                if next_grp0 && gicc.fiq_en() {
                    if gicc.group0_enabled() {
                        cpu_fiq = true;
                    }
                } else if next_grp0 && gicc.group0_enabled() || !next_grp0 && gicc.group1_enabled()
                {
                    cpu_irq = true;
                }
            }

            // Update driven status of FIQ.
            self.signal_fiq(cpu_fiq, cpu_id, fiq_signal);
            // Update driven status of IRQ.
            self.signal_irq(cpu_irq, cpu_id, irq_signal);
        }
    }

    // SignalFIQ(boolean next_fiq, integer cpu_id)
    #[doc(alias("SignalFIQ"))]
    /// Signals an interrupt on the FIQ input to the processor, according to the
    /// value of `next_fiq`.
    fn signal_fiq(&self, next_fiq: bool, cpu_id: u8, fiq_signal: &FiqSignal) {
        if next_fiq {
            fiq_signal.send(cpu_id);
        }
    }

    // SignalIRQ(boolean next_irq, integer cpu_id) // Signals an interrupt on the
    // IRQ input to the processor, according to the value of next_irq.
    #[doc(alias("SignalIRQ"))]
    /// Signals an interrupt on the IRQ input to the processor, according to the
    /// value of `next_irq.`
    fn signal_irq(&self, next_irq: bool, cpu_id: u8, irq_signal: &IrqSignal) {
        if next_irq {
            irq_signal.send(cpu_id);
        }
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct Gicc {
    pub cpu_id: u8,
    /// CPU Interface Control Register.
    pub ctlr: u32,
    /// Interrupt Priority Mask Register.
    pub pmr: u32,
    /// Binary Point Register.
    pub bpr: u32,
    /// Interrupt Acknowledge Register.
    pub iar: u32,
    /// End of Interrupt Register.
    pub eoir: u32,
    /// Running Priority Register.
    pub rpr: u32,
    /// Highest Priority Pending Interrupt Register.
    pub hppir: u32,
    /// Aliased Binary Point Register
    pub abpr: u32,
    /// Aliased Interrupt Acknowledge Register
    pub aiar: u32,
    /// Aliased End of Interrupt Register
    pub aeoir: u32,
    /// Aliased Highest Priority Pending Interrupt Register
    pub ahppir: u32,
    _reserved_0: [u32; 0x34],
    /// CPU Interface Identification Register.
    pub iidr: u32,
    _reserved_1: [u32; 0x3C0],
    /// Deactivate Interrupt Register.
    pub dir: u32,
}

impl Gicc {
    pub const fn new(cpu_id: u8) -> Self {
        Self {
            cpu_id,
            ctlr: 0,
            pmr: 0,
            bpr: MINIMUM_BINARY_POINT as u32,
            iar: 0x000003ff,
            eoir: 0,
            rpr: 0x000000ff,
            hppir: 0x000003ff,
            abpr: MINIMUM_BINARY_POINT as u32 + 1,
            aiar: 0x000003ff,
            aeoir: 0,
            ahppir: 0x000003ff,
            _reserved_0: [0; 0x34],
            iidr: 0x2 << 16,
            _reserved_1: [0; 0x3C0],
            dir: 0,
        }
    }

    #[doc(alias("EnableGrp0"))]
    const fn group0_enabled(&self) -> bool {
        // GICC_CTLR[cpu_id].EnableGrp0 == '1'
        get_bits!(self.ctlr, off = 0, len = 1) == 1
    }

    #[doc(alias("EnableGrp1"))]
    const fn group1_enabled(&self) -> bool {
        // GICC_CTLR[cpu_id].EnableGrp1 == '1'
        get_bits!(self.ctlr, off = 1, len = 1) == 1
    }

    #[doc(alias("AckCtl"))]
    const fn ack_ctl(&self) -> bool {
        // GICC_CTLR[cpu_id].AckCtl == '1'
        get_bits!(self.ctlr, off = 2, len = 1) == 1
    }

    #[doc(alias("FIQEn"))]
    const fn fiq_en(&self) -> bool {
        // GICC_CTLR[cpu_id].FIQEn == '1'
        get_bits!(self.ctlr, off = 3, len = 1) == 1
    }

    #[doc(alias("CBPR"))]
    const fn cbpr(&self) -> bool {
        // GICC_CTLR[cpu_id].CBPR == '1'
        get_bits!(self.ctlr, off = 4, len = 1) == 1
    }

    #[doc(alias("FIQBypDisGrp0"))]
    const fn fiq_byp_dis_grp0(&self) -> bool {
        // GICC_CTLR[cpu_id].FIQBypDisGrp0 == '1'
        get_bits!(self.ctlr, off = 5, len = 1) == 1
    }

    #[doc(alias("IRQBypDisGrp0"))]
    const fn irq_byp_dis_grp0(&self) -> bool {
        // GICC_CTLR[cpu_id].IRQBypDisGrp0 == '1'
        get_bits!(self.ctlr, off = 6, len = 1) == 1
    }

    #[doc(alias("FIQBypDisGrp1"))]
    const fn fiq_byp_dis_grp1(&self) -> bool {
        // GICC_CTLR[cpu_id].FIQBypDisGrp1 == '1'
        get_bits!(self.ctlr, off = 7, len = 1) == 1
    }

    #[doc(alias("IRQBypDisGrp1"))]
    const fn irq_byp_dis_grp1(&self) -> bool {
        // GICC_CTLR[cpu_id].IRQBypDisGrp1 == '1'
        get_bits!(self.ctlr, off = 8, len = 1) == 1
    }

    #[doc(alias("ReadGICC_IAR"))]
    /// Value of `GICC_IAR` read by a CPU access
    fn read_iar(&self, gicd: &mut Gicd, cpu_id: u8) -> u32 {
        let mut pend_id = highest_priority_pending_interrupt(gicd, cpu_id);
        if (gicd.is_grp0_int(pend_id, cpu_id) && (!gicd.group0_enabled() || !self.group0_enabled()))
            || (!gicd.is_grp0_int(pend_id, cpu_id)
                && (!gicd.group1_enabled() || !self.group1_enabled()))
        {
            pend_id = SPURIOUS_INTERRUPT; // If the highest priority isn't
                                          // enabled, then no interrupt
        }
        if pend_id != SPURIOUS_INTERRUPT {
            // An enabled interrupt is pending
            if gicd.is_grp0_int(pend_id, cpu_id) {
                // Highest priority is Group 0
                // if NS_ACCESS {
                //     pend_id = SPURIOUS_INTERRUPT;
                // }
            } else {
                // Highest priority is Group 1
                if !NS_ACCESS && (!self.ack_ctl()) {
                    pend_id = 1022;
                }
            }
        }
        let sgi_id = if pend_id < 16 {
            // 0 .. 15 are Software Generated Interrupts
            unimplemented!() // SGI_CpuID(pend_id) // value is IMPLEMENTATION
                             // DEFINED
        } else {
            // Must be zero for non-SGI interrupts
            0
        };

        // Check that it is not a spurious interrupt
        if pend_id < 1020 {
            // Set active and attempt to clear pending
            gicd.acknowledge_interrupt(pend_id, cpu_id);
        }
        (sgi_id << 10 | pend_id).into()
    }
}
