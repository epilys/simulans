#![no_std]
#![no_main]

extern crate alloc;

mod exceptions;

use core::panic::PanicInfo;

use arm_gic::{
    gicv2::{
        registers::{Gicc, Gicd},
        GicV2,
    },
    irq_enable, IntId, UniqueMmioPointer,
};
use buddy_system_allocator::LockedHeap;
use core::ptr::NonNull;
use flat_device_tree::{Error as FdtError, Fdt};
use smccc::{psci::system_off, Hvc};

use aarch64_cpu::{asm, registers::*};

/// Base memory-mapped address of the primary PL011 UART device.
pub const UART_BASE_ADDRESS: *mut u32 = 0x900_0000 as _;

// Base addresses of the GICv2 distributor and redistributor.
const GICD_BASE_ADDRESS: *mut Gicd = 0x800_0000 as _;
const GICC_BASE_ADDRESS: *mut Gicc = 0x801_0000 as _;

#[global_allocator]
static HEAP_ALLOCATOR: LockedHeap<32> = LockedHeap::new();

use core::fmt::Write;

use pl011_uart::Uart;

// constants required for initializing the UART.
const PL011_BAUD_RATE: u32 = 115200;
const PL011_CLK_IN_HZ: u32 = 50000000;
static mut HEAP: [u8; 0x1000000] = [0; 0x1000000];

#[no_mangle]
extern "C" fn main(x0: u64, _x1: u64, _x2: u64, _x3: u64) {
    // Safe because `HEAP` is only used here and `entry` is only called once.
    unsafe {
        // Give the allocator some memory to allocate.
        HEAP_ALLOCATOR
            .lock()
            .init(HEAP.as_mut_ptr() as usize, HEAP.len());
    }
    // Safe because BASE_ADDRESS is the base of the MMIO region for a UART and is
    // mapped as device memory.

    let mut uart = unsafe { Uart::new(UART_BASE_ADDRESS) };
    uart.init(PL011_CLK_IN_HZ, PL011_BAUD_RATE);
    write!(&mut uart, "Hello world!\n").unwrap();

    // let gicd = unsafe { UniqueMmioPointer::new(NonNull::new(GICD_BASE_ADDRESS).unwrap()) };
    // let gicc = unsafe { NonNull::new(GICC_BASE_ADDRESS).unwrap() };

    let mut gic = unsafe { GicV2::new(GICD_BASE_ADDRESS, GICC_BASE_ADDRESS) };
    let gic_typer = gic.typer();
    writeln!(&mut uart, "gic typer: lockable_spi_count {:?} has_security_extension: {:?} cpu_count: {:?} num_irqs: {:?}", gic_typer.lockable_spi_count(), gic_typer.has_security_extension(), gic_typer.cpu_count(), gic_typer.num_irqs()).unwrap();

    gic.setup();
    gic.set_priority_mask(0xff);
    let timer_irqid = IntId::ppi(30 - 16);
    gic.enable_interrupt(timer_irqid, true);
    gic.set_interrupt_priority(timer_irqid, 0);
    gic.set_trigger(timer_irqid, arm_gic::Trigger::Level);
    let second = CNTFRQ_EL0.get() * 5;
    CNTP_TVAL_EL0.set(second);
    let ctl = CNTP_CTL_EL0.get();
    write!(&mut uart, "ctl = {ctl:#x}\n",).unwrap();
    irq_enable();
    CNTP_CTL_EL0.write(CNTP_CTL_EL0::ENABLE::SET);
    let ctl = CNTP_CTL_EL0.get();
    write!(&mut uart, "ctl = {ctl:#x}\n",).unwrap();
    asm::wfi();

    let status = CNTP_CTL_EL0.read(CNTP_CTL_EL0::ISTATUS);
    write!(&mut uart, "second: {second} status = {status:?}\n",).unwrap();
    let s = alloc::string::String::from(" A heap allocated string ");
    assert_eq!(&s, " A heap allocated string ");
    write!(
        &mut uart,
        "Print an allocated string with a format specifier: {}!\n",
        s
    )
    .unwrap();

    // Safe because the pointer is a valid pointer to unaliased memory.
    match unsafe { Fdt::from_ptr(x0 as *const u8) } {
        Ok(fdt) => {
            write!(&mut uart, "Parsed fdt!\n").unwrap();
            write!(&mut uart, "{} nodes!\n", fdt.all_nodes().count()).unwrap();
            for node in fdt.all_nodes() {
                // Dump information about the node for debugging.
                write!(
                    &mut uart,
                    "{}: {:?}\n",
                    node.name,
                    node.compatible()
                        .map(flat_device_tree::standard_nodes::Compatible::first),
                )
                .unwrap();
                for range in node.reg() {
                    write!(
                        &mut uart,
                        "  {:#018x?}, length {:?}\n",
                        range.starting_address, range.size
                    )
                    .unwrap();
                }
            }
        }
        Err(_err) => {
            write!(&mut uart, "fdt parsing error\n").unwrap();
            //match err {
            //    FdtError::BadMagic => write!(&mut uart, "bad FDT magic value"),
            //    FdtError::BadPtr => write!(&mut uart, "an invalid pointer was passed"),
            //    FdtError::BadCellSize(_) => {
            //        write!(&mut uart, "cells of size cell are currently unsupported")
            //    }
            //    FdtError::BadPropTag((_, _)) => write!(
            //        &mut uart,
            //        "invalid property tag), have: have, expected: exp"
            //    ),
            //    FdtError::BadCell => write!(&mut uart, "Fdterror parsing the property cell value"),
            //    FdtError::BufferTooSmall => write!(
            //        &mut uart,
            //        "the given buffer was too small to contain a FDT header"
            //    ),
            //    FdtError::CpuNoReg => {
            //        write!(&mut uart, "`reg` is a required property of `cpu` nodes")
            //    }
            //    FdtError::CpuNoClockHz => write!(
            //        &mut uart,
            //        "`clock-frequency` is a required property of `cpu` nodes"
            //    ),
            //    FdtError::CpuNoTimebaseHz => write!(
            //        &mut uart,
            //        "`timebase-frequency` is a required property of `cpu` nodes"
            //    ),
            //    FdtError::MappedNoEffectiveAddr => {
            //        write!(
            //            &mut uart,
            //            "`mapped-area` property is missing effective address value"
            //        )
            //    }
            //    FdtError::MappedNoPhysicalAddr => {
            //        write!(
            //            &mut uart,
            //            "`mapped-area` property is missing physical address value"
            //        )
            //    }
            //    FdtError::MappedNoSize => {
            //        write!(&mut uart, "`mapped-area` property is missing size value")
            //    }
            //    FdtError::MemoryNoInitialMapped => {
            //        write!(
            //            &mut uart,
            //            "`memory` node is missing an `initial-mapped-area` property"
            //        )
            //    }
            //    FdtError::MissingProperty => write!(&mut uart, "node is missing a property entry"),
            //    FdtError::MissingRoot => write!(&mut uart, "missing `root` node"),
            //    FdtError::MissingChosen => write!(&mut uart, "missing `chosen` node"),
            //    FdtError::MissingMemory => write!(&mut uart, "missing `memory` node"),
            //}
            //.unwrap();
        }
    }

    write!(&mut uart, "Halting the machine.\n").unwrap();
    system_off::<Hvc>().unwrap();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut uart = unsafe { Uart::new(UART_BASE_ADDRESS) };
    uart.init(PL011_CLK_IN_HZ, PL011_BAUD_RATE);
    write!(&mut uart, "{}\n", info).unwrap();
    system_off::<Hvc>().unwrap();
    loop {}
}
