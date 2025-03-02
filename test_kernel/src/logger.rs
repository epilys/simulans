//! Log implementation using the UART.

use crate::UART_BASE_ADDRESS;

use core::fmt::Write;
use log::{LevelFilter, Log, Metadata, Record, SetLoggerError};
use pl011_uart::Uart;
use spin::mutex::SpinMutex;

static LOGGER: Logger = Logger {
    uart: SpinMutex::new(None),
};

struct Logger {
    uart: SpinMutex<Option<Uart>>,
}

/// Initialises UART logger.
pub fn init(max_level: LevelFilter) -> Result<(), SetLoggerError> {
    // constants required for initializing the UART.
    const PL011_BAUD_RATE: u32 = 115200;
    const PL011_CLK_IN_HZ: u32 = 50000000;

    // Safe because BASE_ADDRESS is the base of the MMIO region for a UART and is mapped as device
    // memory.
    let mut uart = unsafe { Uart::new(UART_BASE_ADDRESS) };
    uart.init(PL011_CLK_IN_HZ, PL011_BAUD_RATE);
    LOGGER.uart.lock().replace(uart);

    log::set_logger(&LOGGER)?;
    log::set_max_level(max_level);
    Ok(())
}

impl Log for Logger {
    fn enabled(&self, _metadata: &Metadata) -> bool {
        true
    }

    fn log(&self, record: &Record) {
        writeln!(
            LOGGER.uart.lock().as_mut().unwrap(),
            "# [{}] {}",
            record.level(),
            record.args()
        )
        .unwrap();
    }

    fn flush(&self) {}
}

pub fn print(args: core::fmt::Arguments<'_>) {
    write!(LOGGER.uart.lock().as_mut().unwrap(), "{}", args).unwrap();
}

#[macro_export]
macro_rules! print {
    ($($arg:tt)*) => {{
        $crate::logger::print(format_args!($($arg)*));
    }};
}

#[macro_export]
macro_rules! println {
    () => {
        $crate::print!("\n");
    };
    ($($arg:tt)*) => {{
        $crate::print!("{}", format_args!("{}\n", format_args!($($arg)*)));
    }};
}
