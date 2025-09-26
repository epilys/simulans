//! Exception handlers.

use core::arch::asm;

use aarch64_cpu::{asm, registers::*};
use core::fmt::Write;
use log::error;
use pl011_uart::Uart;
use smccc::{psci::system_off, Hvc};

/// Base memory-mapped address of the primary PL011 UART device.
const UART_BASE_ADDRESS: *mut u32 = 0x900_0000 as _;
const PL011_BAUD_RATE: u32 = 115200;
const PL011_CLK_IN_HZ: u32 = 50000000;

#[no_mangle]
extern "C" fn sync_exception_current(_elr: u64, _spsr: u64) {
    error!("sync_exception_current");
    print_esr();
    system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn irq_current(_elr: u64, _spsr: u64) {
    let mut uart = unsafe { Uart::new(UART_BASE_ADDRESS) };
    uart.init(PL011_CLK_IN_HZ, PL011_BAUD_RATE);
    write!(&mut uart, "irq_current\n").unwrap();
    CNTP_CTL_EL0.write(CNTP_CTL_EL0::ENABLE::CLEAR);
    // system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn fiq_current(_elr: u64, _spsr: u64) {
    error!("fiq_current");
    system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn serr_current(_elr: u64, _spsr: u64) {
    error!("serr_current");
    print_esr();
    system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn sync_lower(_elr: u64, _spsr: u64) {
    error!("sync_lower");
    print_esr();
    system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn irq_lower(_elr: u64, _spsr: u64) {
    error!("irq_lower");
    system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn fiq_lower(_elr: u64, _spsr: u64) {
    error!("fiq_lower");
    system_off::<Hvc>().unwrap();
}

#[no_mangle]
extern "C" fn serr_lower(_elr: u64, _spsr: u64) {
    error!("serr_lower");
    print_esr();
    system_off::<Hvc>().unwrap();
}

#[inline]
fn print_esr() {
    let mut esr: u64;
    unsafe {
        asm!("mrs {esr}, esr_el1", esr = out(reg) esr);
    }
    log::error!("esr={:#08x}", esr);
}
