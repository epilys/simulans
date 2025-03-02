#![no_std]
#![no_main]

extern crate alloc;

mod exceptions;
mod logger;

use buddy_system_allocator::LockedHeap;
use core::panic::PanicInfo;
use flat_device_tree::Fdt;
use smccc::{psci::system_off, Hvc};

/// Base memory-mapped address of the primary PL011 UART device.
pub const UART_BASE_ADDRESS: *mut u32 = 0x900_0000 as _;

#[global_allocator]
static HEAP_ALLOCATOR: LockedHeap<32> = LockedHeap::new();

static mut HEAP: [u8; 0x1000000] = [0; 0x1000000];
#[no_mangle]
extern "C" fn main(x0: u64, _x1: u64, _x2: u64, _x3: u64) {
    logger::init(log::LevelFilter::Off).unwrap();
    // Safe because `HEAP` is only used here and `entry` is only called once.
    unsafe {
        // Give the allocator some memory to allocate.
        HEAP_ALLOCATOR
            .lock()
            .init(HEAP.as_mut_ptr() as usize, HEAP.len());
    }

    // Safe because the pointer is a valid pointer to unaliased memory.
    let fdt = unsafe { Fdt::from_ptr(x0 as *const u8).unwrap() };

    for node in fdt.all_nodes() {
        // Dump information about the node for debugging.
        log::trace!(
            "{}: {:?}",
            node.name,
            node.compatible()
                .map(flat_device_tree::standard_nodes::Compatible::first),
        );
        for range in node.reg() {
            log::trace!(
                "  {:#018x?}, length {:?}",
                range.starting_address,
                range.size
            );
        }
    }
    println!("Hello world!");
    println!("Halting the machine.");
    system_off::<Hvc>().unwrap();
}

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    log::error!("{}", info);
    system_off::<Hvc>().unwrap();
    loop {}
}
