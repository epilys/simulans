// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Emulated PL011 UART.

use std::sync::{Arc, Mutex};

use crate::{
    devices::{CharBackendExt, CharBackendOps, DeviceOps, MemoryTxResult},
    machine::{
        interrupts::{InterruptGenerator, InterruptRequest, Interrupts},
        CharBackendWriter,
    },
    memory::{Address, MemoryRegion, MemorySize, Width},
    tracing,
};

// TODO: You must disable the UART before any of the control registers are
// reprogrammed. When the UART is disabled in the middle of transmission or
// reception, it completes the current character before stopping

/// Max FIFO depth.
pub const PL011_FIFO_DEPTH: u32 = 16;

/// Device ID that the UART reports.
#[derive(Clone, Copy)]
struct DeviceId(&'static [u8; 8]);

impl std::ops::Index<u64> for DeviceId {
    type Output = u8;

    fn index(&self, idx: u64) -> &Self::Output {
        &self.0[idx as usize]
    }
}

#[repr(transparent)]
#[derive(Debug, Default)]
/// 32-bit indexed data FIFO.
pub struct Fifo([registers::Data; PL011_FIFO_DEPTH as usize]);

impl std::ops::IndexMut<u32> for Fifo {
    fn index_mut(&mut self, idx: u32) -> &mut Self::Output {
        &mut self.0[idx as usize]
    }
}

impl std::ops::Index<u32> for Fifo {
    type Output = registers::Data;

    fn index(&self, idx: u32) -> &Self::Output {
        &self.0[idx as usize]
    }
}

#[repr(C)]
#[derive(Debug, Default)]
/// Register file.
pub struct PL011Registers {
    /// Flag register.
    #[doc(alias = "fr")]
    pub flags: registers::Flags,
    #[doc(alias = "lcr")]
    /// Line control register.
    pub line_control: registers::LineControl,
    #[doc(alias = "rsr")]
    /// Receive-status-error-clear register.
    pub receive_status_error_clear: registers::ReceiveStatusErrorClear,
    #[doc(alias = "cr")]
    /// Control register.
    pub control: registers::Control,
    pub dmacr: u32,
    pub int_enabled: u32,
    pub int_level: u32,
    pub read_fifo: Fifo,
    pub ilpr: u32,
    pub ibrd: u32,
    pub fbrd: u32,
    pub ifl: u32,
    pub read_pos: u32,
    pub read_count: u32,
    pub read_trigger: u32,
}

#[derive(Debug)]
/// PL011 Device Model
pub struct PL011State {
    /// Device ID.
    pub device_id: u64,
    address: Address,
    char_backend: CharBackendWriter,
    irq_generator: InterruptGenerator,
}

impl PL011State {
    const DEVICE_ID: DeviceId = DeviceId(&[0x11, 0x10, 0x14, 0x00, 0x0d, 0xf0, 0x05, 0xb1]);
}

impl crate::devices::Device for PL011State {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn into_memory_regions(self) -> Vec<MemoryRegion> {
        let Self {
            device_id,
            address,
            irq_generator,
            char_backend,
        } = self;

        vec![MemoryRegion::new_io(
            MemorySize::new(0x1000).unwrap(),
            address,
            Box::new(PL011MemoryOps {
                device_id,
                char_backend,
                regs: Default::default(),
                interrupts: [33; 6],
                irq_generator,
            }),
        )
        .unwrap()]
    }
}

impl PL011Registers {
    pub(self) fn read(&mut self, offset: RegisterOffset) -> (bool, u32) {
        use RegisterOffset::*;

        let mut update = false;
        let result = match offset {
            DR => {
                self.flags.set_receive_fifo_full(false);
                let c = self.read_fifo[self.read_pos];
                if self.read_count > 0 {
                    self.read_count -= 1;
                    self.read_pos = (self.read_pos + 1) & (self.fifo_depth() - 1);
                }
                if self.read_count == 0 {
                    self.flags.set_receive_fifo_empty(true);
                }
                if self.read_count + 1 == self.read_trigger {
                    self.int_level &= !Interrupt::RX.0;
                }
                // Update error bits.
                self.receive_status_error_clear.set_from_data(c);
                update = true;
                u32::from(c)
            }
            RSR => u32::from(self.receive_status_error_clear),
            FR => u32::from(self.flags),
            FBRD => self.fbrd,
            ILPR => self.ilpr,
            IBRD => self.ibrd,
            LCR_H => u32::from(self.line_control),
            CR => u32::from(self.control),
            FLS => self.ifl,
            IMSC => self.int_enabled,
            RIS => self.int_level,
            MIS => self.int_level & self.int_enabled,
            ICR => {
                // "The UARTICR Register is the interrupt clear register and is write-only"
                // Source: ARM DDI 0183G 3.3.13 Interrupt Clear Register, UARTICR
                0
            }
            DMACR => self.dmacr,
        };
        (update, result)
    }

    pub(self) fn write(&mut self, offset: RegisterOffset, value: u32) -> bool {
        use RegisterOffset::*;

        tracing::event!(
            target: tracing::TraceItem::Pl011.as_str(),
            tracing::Level::TRACE,
            kind = "write",
            ?offset,
            value = ?tracing::BinaryHex(value),
        );
        match offset {
            DR => {
                // interrupts always checked
                let _ = self.loopback_tx(value.into());
                self.int_level |= Interrupt::TX.0;
                return true;
            }
            RSR => {
                self.receive_status_error_clear = 0.into();
            }
            FR => {
                // flag writes are ignored
            }
            ILPR => {
                self.ilpr = value;
            }
            IBRD => {
                self.ibrd = value;
            }
            FBRD => {
                self.fbrd = value;
            }
            LCR_H => {
                let new_val: registers::LineControl = value.into();
                // Reset the FIFO state on FIFO enable or disable
                if self.line_control.fifos_enabled() != new_val.fifos_enabled() {
                    self.reset_rx_fifo();
                    self.reset_tx_fifo();
                }
                let update = (self.line_control.send_break() != new_val.send_break()) && {
                    let break_enable = new_val.send_break();
                    // let _ = char_backend.send_break(break_enable);
                    self.loopback_break(break_enable)
                };
                self.line_control = new_val;
                self.set_read_trigger();
                return update;
            }
            CR => {
                // ??? Need to implement the enable bit.
                self.control = value.into();
                return self.loopback_mdmctrl();
            }
            FLS => {
                self.ifl = value;
                self.set_read_trigger();
            }
            IMSC => {
                self.int_enabled = value;
                return true;
            }
            RIS => {}
            MIS => {}
            ICR => {
                self.int_level &= !value;
                return true;
            }
            DMACR => {
                self.dmacr = value;
                if value & 3 > 0 {
                    tracing::error!("pl011: DMA not implemented");
                }
            }
        }
        false
    }

    #[inline]
    #[must_use]
    fn loopback_tx(&mut self, value: registers::Data) -> bool {
        // Caveat:
        //
        // In real hardware, TX loopback happens at the serial-bit level
        // and then reassembled by the RX logics back into bytes and placed
        // into the RX fifo. That is, loopback happens after TX fifo.
        //
        // Because the real hardware TX fifo is time-drained at the frame
        // rate governed by the configured serial format, some loopback
        // bytes in TX fifo may still be able to get into the RX fifo
        // that could be full at times while being drained at software
        // pace.
        //
        // In such scenario, the RX draining pace is the major factor
        // deciding which loopback bytes get into the RX fifo, unless
        // hardware flow-control is enabled.
        //
        // For simplicity, the above described is not emulated.
        self.loopback_enabled() && self.put_fifo(value)
    }

    #[must_use]
    fn loopback_mdmctrl(&mut self) -> bool {
        if !self.loopback_enabled() {
            return false;
        }

        // Loopback software-driven modem control outputs to modem status inputs:
        //   FR.RI  <= CR.Out2
        //   FR.DCD <= CR.Out1
        //   FR.CTS <= CR.RTS
        //   FR.DSR <= CR.DTR
        //
        // The loopback happens immediately even if this call is triggered
        // by setting only CR.LBE.
        //
        // CTS/RTS updates due to enabled hardware flow controls are not
        // dealt with here.

        self.flags.set_ring_indicator(self.control.out_2());
        self.flags.set_data_carrier_detect(self.control.out_1());
        self.flags.set_clear_to_send(self.control.request_to_send());
        self.flags
            .set_data_set_ready(self.control.data_transmit_ready());

        // Change interrupts based on updated FR
        let mut il = self.int_level;

        il &= !Interrupt::MS.0;

        if self.flags.data_set_ready() {
            il |= Interrupt::DSR.0;
        }
        if self.flags.data_carrier_detect() {
            il |= Interrupt::DCD.0;
        }
        if self.flags.clear_to_send() {
            il |= Interrupt::CTS.0;
        }
        if self.flags.ring_indicator() {
            il |= Interrupt::RI.0;
        }
        self.int_level = il;
        true
    }

    #[inline]
    fn loopback_break(&mut self, enable: bool) -> bool {
        enable && self.loopback_tx(registers::Data::BREAK)
    }

    #[inline]
    const fn set_read_trigger(&mut self) {
        self.read_trigger = 1;
    }

    pub fn reset(&mut self) {
        self.line_control.reset();
        self.receive_status_error_clear.reset();
        self.dmacr = 0;
        self.int_enabled = 0;
        self.int_level = 0;
        self.ilpr = 0;
        self.ibrd = 0;
        self.fbrd = 0;
        self.read_trigger = 1;
        self.ifl = 0x12;
        self.control.reset();
        self.flags.reset();
        self.reset_rx_fifo();
        self.reset_tx_fifo();
    }

    pub fn reset_rx_fifo(&mut self) {
        self.read_count = 0;
        self.read_pos = 0;

        // Reset FIFO flags
        self.flags.set_receive_fifo_full(false);
        self.flags.set_receive_fifo_empty(true);
    }

    pub fn reset_tx_fifo(&mut self) {
        // Reset FIFO flags
        self.flags.set_transmit_fifo_full(false);
        self.flags.set_transmit_fifo_empty(true);
    }

    #[inline]
    pub fn fifo_enabled(&self) -> bool {
        self.line_control.fifos_enabled() == registers::Mode::FIFO
    }

    #[inline]
    pub fn loopback_enabled(&self) -> bool {
        self.control.enable_loopback()
    }

    #[inline]
    pub fn fifo_depth(&self) -> u32 {
        // Note: FIFO depth is expected to be power-of-2
        if self.fifo_enabled() {
            return PL011_FIFO_DEPTH;
        }
        1
    }

    #[must_use]
    pub fn put_fifo(&mut self, value: registers::Data) -> bool {
        let depth = self.fifo_depth();
        assert!(depth > 0);
        let slot = (self.read_pos + self.read_count) & (depth - 1);
        self.read_fifo[slot] = value;
        self.read_count += 1;
        self.flags.set_receive_fifo_empty(false);
        if self.read_count == depth {
            self.flags.set_receive_fifo_full(true);
        }

        if self.read_count == self.read_trigger {
            self.int_level |= Interrupt::RX.0;
            return true;
        }
        false
    }

    fn receive(&mut self, buf: &[u8], interrupts: &[u16], generator: &InterruptGenerator) {
        if self.loopback_enabled() {
            // In loopback mode, the RX input signal is internally disconnected
            // from the entire receiving logics; thus, all inputs are ignored,
            // and BREAK detection on RX input signal is also not performed.
            // return;
        }

        let mut update_irq = false;
        for &c in buf {
            let c: u32 = c.into();
            update_irq |= self.put_fifo(c.into());
        }

        if update_irq {
            self.update(interrupts, generator);
        }
    }

    fn update(&self, interrupts: &[u16], generator: &InterruptGenerator) {
        /// Which bits in the interrupt status matter for each outbound IRQ line
        /// ?
        const IRQMASK: [u32; 6] = [
            // combined IRQ
            Interrupt::E.0 | Interrupt::MS.0 | Interrupt::RT.0 | Interrupt::TX.0 | Interrupt::RX.0,
            Interrupt::RX.0,
            Interrupt::TX.0,
            Interrupt::RT.0,
            Interrupt::MS.0,
            Interrupt::E.0,
        ];
        let flags = self.int_level & self.int_enabled;
        let mut any = None;
        for (irq, i) in interrupts.iter().zip(IRQMASK) {
            if flags & i > 0 {
                any = Some(*irq);
            }
        }
        if let Some(irq) = any {
            _ = generator.irq_sender.try_send(InterruptRequest {
                interrupt_id: irq,
                cpu_id: None,
            });
        }
    }
}

#[derive(Debug)]
struct PL011MemoryOps {
    device_id: u64,
    char_backend: CharBackendWriter,
    interrupts: [u16; 6],
    regs: Arc<Mutex<PL011Registers>>,
    irq_generator: InterruptGenerator,
}

impl DeviceOps for PL011MemoryOps {
    fn id(&self) -> u64 {
        self.device_id
    }

    fn read(&self, offset: u64, width: Width) -> MemoryTxResult<u64> {
        Ok(match RegisterOffset::try_from(offset) {
            Err(v) if (0x3f8..0x400).contains(&(v >> 2)) => {
                let device_id = PL011State::DEVICE_ID;
                u64::from(device_id[(offset - 0xfe0) >> 2])
            }
            Err(_) => {
                tracing::error!("pl011_read: Bad offset 0x{:x} width {:?}", offset, width);
                0
            }
            Ok(field) => {
                let result = {
                    let Self {
                        ref interrupts,
                        ref irq_generator,
                        ref regs,
                        ..
                    } = self;
                    let mut regs = regs.lock().unwrap();
                    let (update_irq, result) = regs.read(field);
                    let remainder = offset - field as u64;
                    if update_irq {
                        regs.update(interrupts, irq_generator);
                        drop(regs);
                        // self.char_backend.accept_input();
                    }
                    if remainder != 0 {
                        assert!(matches!(width, Width::_32 | Width::_16), "{width:?}");
                    }
                    result
                };
                tracing::event!(
                    target: tracing::TraceItem::Pl011.as_str(),
                    tracing::Level::TRACE,
                    kind = "read",
                    offset = ?tracing::Hex(offset),
                    ?field,
                    ?width,
                    ?result,
                );
                result.into()
            }
        })
    }

    fn write(&self, offset: u64, value: u64, _width: Width) -> MemoryTxResult {
        if let Ok(field) = RegisterOffset::try_from(offset) {
            let Self {
                ref interrupts,
                ref irq_generator,
                ref regs,
                ref char_backend,
                ..
            } = self;
            {
                if field == RegisterOffset::DR {
                    // ??? Check if transmitter is enabled.
                    let ch: [u8; 1] = [value as u8];
                    (char_backend.write_all)(&ch);
                }
            }

            let mut regs = regs.lock().unwrap();
            let update_irq = regs.write(field, value as u32);
            if update_irq {
                regs.update(interrupts, irq_generator);
            }
        } else {
            tracing::error!("write bad offset 0x{offset:x} value 0x{value:x}");
        }
        Ok(())
    }

    #[inline(always)]
    fn supports_char_backend(&'_ self) -> Option<CharBackendOps<'_>> {
        Some(self)
    }
}

impl CharBackendExt for PL011MemoryOps {
    fn receive(&self, buf: &[u8]) {
        let Self {
            ref interrupts,
            ref irq_generator,
            ref regs,
            ..
        } = self;
        let mut regs = regs.lock().unwrap();
        regs.receive(buf, interrupts, irq_generator);
    }
}

impl PL011State {
    pub fn new(
        device_id: u64,
        address: Address,
        char_backend: CharBackendWriter,
        interrupts: &Interrupts,
    ) -> Self {
        let irq_generator = interrupts.generator.clone();
        Self {
            device_id,
            address,
            char_backend,
            irq_generator,
        }
    }
}

use registers::*;

mod registers {
    // Copyright 2024, Linaro Limited
    // Author(s): Manos Pitsidianakis <manos.pitsidianakis@linaro.org>
    // SPDX-License-Identifier: GPL-2.0-or-later

    //! Device registers exposed as typed structs which are backed by arbitrary
    //! integer bitmaps. [`Data`], [`Control`], [`LineControl`], etc.

    use bilge::prelude::*;

    /// Offset of each register from the base memory address of the device.
    ///
    /// # Source
    /// ARM DDI 0183G, Table 3-1 p.3-3
    #[doc(alias = "offset")]
    #[allow(non_camel_case_types, clippy::upper_case_acronyms)]
    #[repr(u64)]
    #[derive(Debug, Eq, PartialEq, Copy, Clone)]
    pub enum RegisterOffset {
        /// Data Register
        ///
        /// A write to this register initiates the actual data transmission
        #[doc(alias = "UARTDR")]
        DR = 0x000,
        /// Receive Status Register or Error Clear Register
        #[doc(alias = "UARTRSR")]
        #[doc(alias = "UARTECR")]
        RSR = 0x004,
        /// Flag Register
        ///
        /// A read of this register shows if transmission is complete
        #[doc(alias = "UARTFR")]
        FR = 0x018,
        /// Fractional Baud Rate Register
        ///
        /// responsible for baud rate speed
        #[doc(alias = "UARTFBRD")]
        FBRD = 0x028,
        /// `IrDA` Low-Power Counter Register
        #[doc(alias = "UARTILPR")]
        ILPR = 0x020,
        /// Integer Baud Rate Register
        ///
        /// Responsible for baud rate speed
        #[doc(alias = "UARTIBRD")]
        IBRD = 0x024,
        /// line control register (data frame format)
        #[doc(alias = "UARTLCR_H")]
        LCR_H = 0x02C,
        /// Toggle UART, transmission or reception
        #[doc(alias = "UARTCR")]
        CR = 0x30,
        /// Interrupt FIFO Level Select Register
        #[doc(alias = "UARTIFLS")]
        FLS = 0x34,
        /// Interrupt Mask Set/Clear Register
        #[doc(alias = "UARTIMSC")]
        IMSC = 0x38,
        /// Raw Interrupt Status Register
        #[doc(alias = "UARTRIS")]
        RIS = 0x3C,
        /// Masked Interrupt Status Register
        #[doc(alias = "UARTMIS")]
        MIS = 0x040,
        /// Interrupt Clear Register
        #[doc(alias = "UARTICR")]
        ICR = 0x044,
        /// DMA control Register
        #[doc(alias = "UARTDMACR")]
        DMACR = 0x048,
        ///// Reserved, offsets `0x04C` to `0x07C`.
        //Reserved = 0x04C,
    }

    impl std::convert::TryFrom<u64> for RegisterOffset {
        type Error = u64;

        fn try_from(value: u64) -> std::result::Result<Self, Self::Error> {
            match value {
                (0x00..0x04) => Ok(Self::DR),
                (0x04..0x08) => Ok(Self::RSR),
                (0x18..0x1c) => Ok(Self::FR),
                (0x20..0x24) => Ok(Self::ILPR),
                (0x24..0x28) => Ok(Self::IBRD),
                (0x28..0x2c) => Ok(Self::FBRD),
                (0x2C..0x30) => Ok(Self::LCR_H),
                (0x30..0x34) => Ok(Self::CR),
                (0x34..0x38) => Ok(Self::FLS),
                (0x38..0x3c) => Ok(Self::IMSC),
                (0x3C..0x40) => Ok(Self::RIS),
                (0x40..0x44) => Ok(Self::MIS),
                (0x44..0x48) => Ok(Self::ICR),
                (0x48..0x4c) => Ok(Self::DMACR),
                _ => Err(value),
            }
        }
    }

    /// Receive Status Register / Data Register common error bits
    ///
    /// The `UARTRSR` register is updated only when a read occurs
    /// from the `UARTDR` register with the same status information
    /// that can also be obtained by reading the `UARTDR` register
    #[bitsize(8)]
    #[derive(Clone, Copy, Default, DebugBits, FromBits)]
    pub struct Errors {
        pub framing_error: bool,
        pub parity_error: bool,
        pub break_error: bool,
        pub overrun_error: bool,
        _reserved_unpredictable: u4,
    }

    // TODO: FIFO Mode has different semantics
    /// Data Register, `UARTDR`
    ///
    /// The `UARTDR` register is the data register.
    ///
    /// For words to be transmitted:
    ///
    /// - if the FIFOs are enabled, data written to this location is pushed onto
    ///   the transmit
    /// FIFO
    /// - if the FIFOs are not enabled, data is stored in the transmitter
    ///   holding register (the
    /// bottom word of the transmit FIFO).
    ///
    /// The write operation initiates transmission from the UART. The data is
    /// prefixed with a start bit, appended with the appropriate parity bit
    /// (if parity is enabled), and a stop bit. The resultant word is then
    /// transmitted.
    ///
    /// For received words:
    ///
    /// - if the FIFOs are enabled, the data byte and the 4-bit status (break,
    ///   frame, parity,
    /// and overrun) is pushed onto the 12-bit wide receive FIFO
    /// - if the FIFOs are not enabled, the data byte and status are stored in
    ///   the receiving
    /// holding register (the bottom word of the receive FIFO).
    ///
    /// The received data byte is read by performing reads from the `UARTDR`
    /// register along with the corresponding status information. The status
    /// information can also be read by a read of the `UARTRSR/UARTECR`
    /// register.
    ///
    /// # Note
    ///
    /// You must disable the UART before any of the control registers are
    /// reprogrammed. When the UART is disabled in the middle of
    /// transmission or reception, it completes the current character before
    /// stopping.
    ///
    /// # Source
    /// ARM DDI 0183G 3.3.1 Data Register, UARTDR
    #[bitsize(32)]
    #[derive(Clone, Copy, Default, DebugBits, FromBits)]
    #[doc(alias = "UARTDR")]
    pub struct Data {
        pub data: u8,
        pub errors: Errors,
        _reserved: u16,
    }

    impl Data {
        // bilge is not very const-friendly, unfortunately
        pub const BREAK: Self = Self { value: 1 << 10 };
    }

    // TODO: FIFO Mode has different semantics
    /// Receive Status Register / Error Clear Register, `UARTRSR/UARTECR`
    ///
    /// The UARTRSR/UARTECR register is the receive status register/error clear
    /// register. Receive status can also be read from the `UARTRSR`
    /// register. If the status is read from this register, then the status
    /// information for break, framing and parity corresponds to the
    /// data character read from the [Data register](Data), `UARTDR` prior to
    /// reading the UARTRSR register. The status information for overrun is
    /// set immediately when an overrun condition occurs.
    ///
    ///
    /// # Note
    /// The received data character must be read first from the [Data
    /// Register](Data), `UARTDR` before reading the error status associated
    /// with that data character from the `UARTRSR` register. This read
    /// sequence cannot be reversed, because the `UARTRSR` register is
    /// updated only when a read occurs from the `UARTDR` register. However,
    /// the status information can also be obtained by reading the `UARTDR`
    /// register
    ///
    /// # Source
    /// ARM DDI 0183G 3.3.2 Receive Status Register/Error Clear Register,
    /// UARTRSR/UARTECR
    #[bitsize(32)]
    #[derive(Clone, Copy, DebugBits, FromBits)]
    pub struct ReceiveStatusErrorClear {
        pub errors: Errors,
        _reserved_unpredictable: u24,
    }

    impl ReceiveStatusErrorClear {
        pub fn set_from_data(&mut self, data: Data) {
            self.set_errors(data.errors());
        }

        pub fn reset(&mut self) {
            // All the bits are cleared to 0 on reset.
            *self = Self::default();
        }
    }

    impl Default for ReceiveStatusErrorClear {
        fn default() -> Self {
            0.into()
        }
    }

    #[bitsize(32)]
    #[derive(Clone, Copy, DebugBits, FromBits)]
    /// Flag Register, `UARTFR`
    #[doc(alias = "UARTFR")]
    pub struct Flags {
        /// CTS Clear to send. This bit is the complement of the UART clear to
        /// send, `nUARTCTS`, modem status input. That is, the bit is 1
        /// when `nUARTCTS` is LOW.
        pub clear_to_send: bool,
        /// DSR Data set ready. This bit is the complement of the UART data set
        /// ready, `nUARTDSR`, modem status input. That is, the bit is 1 when
        /// `nUARTDSR` is LOW.
        pub data_set_ready: bool,
        /// DCD Data carrier detect. This bit is the complement of the UART data
        /// carrier detect, `nUARTDCD`, modem status input. That is, the bit is
        /// 1 when `nUARTDCD` is LOW.
        pub data_carrier_detect: bool,
        /// BUSY UART busy. If this bit is set to 1, the UART is busy
        /// transmitting data. This bit remains set until the complete
        /// byte, including all the stop bits, has been sent from the
        /// shift register. This bit is set as soon as the transmit FIFO
        /// becomes non-empty, regardless of whether the UART is enabled
        /// or not.
        pub busy: bool,
        /// RXFE Receive FIFO empty. The meaning of this bit depends on the
        /// state of the FEN bit in the `UARTLCR_H` register. If the FIFO
        /// is disabled, this bit is set when the receive holding
        /// register is empty. If the FIFO is enabled, the RXFE bit is
        /// set when the receive FIFO is empty.
        pub receive_fifo_empty: bool,
        /// TXFF Transmit FIFO full. The meaning of this bit depends on the
        /// state of the FEN bit in the `UARTLCR_H` register. If the FIFO
        /// is disabled, this bit is set when the transmit holding
        /// register is full. If the FIFO is enabled, the TXFF bit is
        /// set when the transmit FIFO is full.
        pub transmit_fifo_full: bool,
        /// RXFF Receive FIFO full. The meaning of this bit depends on the state
        /// of the FEN bit in the `UARTLCR_H` register. If the FIFO is
        /// disabled, this bit is set when the receive holding register
        /// is full. If the FIFO is enabled, the RXFF bit is set when
        /// the receive FIFO is full.
        pub receive_fifo_full: bool,
        /// Transmit FIFO empty. The meaning of this bit depends on the state of
        /// the FEN bit in the [Line Control register](LineControl),
        /// `UARTLCR_H`. If the FIFO is disabled, this bit is set when the
        /// transmit holding register is empty. If the FIFO is enabled,
        /// the TXFE bit is set when the transmit FIFO is empty. This
        /// bit does not indicate if there is data in the transmit shift
        /// register.
        pub transmit_fifo_empty: bool,
        /// `RI`, is `true` when `nUARTRI` is `LOW`.
        pub ring_indicator: bool,
        _reserved_zero_no_modify: u23,
    }

    impl Flags {
        pub fn reset(&mut self) {
            *self = Self::default();
        }
    }

    impl Default for Flags {
        fn default() -> Self {
            let mut ret: Self = 0.into();
            // After reset TXFF, RXFF, and BUSY are 0, and TXFE and RXFE are 1
            ret.set_receive_fifo_empty(true);
            ret.set_transmit_fifo_empty(true);
            ret.set_receive_fifo_full(false);
            ret.set_transmit_fifo_full(false);
            ret
        }
    }

    #[bitsize(32)]
    #[derive(Clone, Copy, DebugBits, FromBits)]
    /// Line Control Register, `UARTLCR_H`
    #[doc(alias = "UARTLCR_H")]
    pub struct LineControl {
        /// BRK Send break.
        ///
        /// If this bit is set to `1`, a low-level is continually output on the
        /// `UARTTXD` output, after completing transmission of the
        /// current character. For the proper execution of the break command,
        /// the software must set this bit for at least two complete
        /// frames. For normal use, this bit must be cleared to `0`.
        pub send_break: bool,
        /// 1 PEN Parity enable:
        ///
        /// - 0 = parity is disabled and no parity bit added to the data frame
        /// - 1 = parity checking and generation is enabled.
        ///
        /// See Table 3-11 on page 3-14 for the parity truth table.
        pub parity_enabled: bool,
        /// EPS Even parity select. Controls the type of parity the UART uses
        /// during transmission and reception:
        /// - 0 = odd parity. The UART generates or checks for an odd number of
        ///   1s in the data and parity bits.
        /// - 1 = even parity. The UART generates or checks for an even number
        ///   of 1s in the data and parity bits.
        /// This bit has no effect when the `PEN` bit disables parity checking
        /// and generation. See Table 3-11 on page 3-14 for the parity
        /// truth table.
        pub parity: Parity,
        /// 3 STP2 Two stop bits select. If this bit is set to 1, two stop bits
        /// are transmitted at the end of the frame. The receive
        /// logic does not check for two stop bits being received.
        pub two_stops_bits: bool,
        /// FEN Enable FIFOs:
        /// 0 = FIFOs are disabled (character mode) that is, the FIFOs become
        /// 1-byte-deep holding registers 1 = transmit and receive FIFO
        /// buffers are enabled (FIFO mode).
        pub fifos_enabled: Mode,
        /// WLEN Word length. These bits indicate the number of data bits
        /// transmitted or received in a frame as follows: b11 = 8 bits
        /// b10 = 7 bits
        /// b01 = 6 bits
        /// b00 = 5 bits.
        pub word_length: WordLength,
        /// 7 SPS Stick parity select.
        /// 0 = stick parity is disabled
        /// 1 = either:
        /// • if the EPS bit is 0 then the parity bit is transmitted and checked
        /// as a 1 • if the EPS bit is 1 then the parity bit is
        /// transmitted and checked as a 0. This bit has no effect when
        /// the PEN bit disables parity checking and generation. See Table 3-11
        /// on page 3-14 for the parity truth table.
        pub sticky_parity: bool,
        /// 31:8 - Reserved, do not modify, read as zero.
        _reserved_zero_no_modify: u24,
    }

    impl LineControl {
        pub fn reset(&mut self) {
            // All the bits are cleared to 0 when reset.
            *self = 0.into();
        }
    }

    impl Default for LineControl {
        fn default() -> Self {
            0.into()
        }
    }

    #[bitsize(1)]
    #[derive(Clone, Copy, Debug, Eq, FromBits, PartialEq)]
    /// `EPS` "Even parity select", field of [Line Control
    /// register](LineControl).
    pub enum Parity {
        /// - 0 = odd parity. The UART generates or checks for an odd number of
        ///   1s in the data and parity bits.
        Odd = 0,
        /// - 1 = even parity. The UART generates or checks for an even number
        ///   of 1s in the data and parity bits.
        Even = 1,
    }

    #[bitsize(1)]
    #[derive(Clone, Copy, Debug, Eq, FromBits, PartialEq)]
    /// `FEN` "Enable FIFOs" or Device mode, field of [Line Control
    /// register](LineControl).
    pub enum Mode {
        /// 0 = FIFOs are disabled (character mode) that is, the FIFOs become
        /// 1-byte-deep holding registers
        Character = 0,
        /// 1 = transmit and receive FIFO buffers are enabled (FIFO mode).
        FIFO = 1,
    }

    #[bitsize(2)]
    #[derive(Clone, Copy, Debug, Eq, FromBits, PartialEq)]
    /// `WLEN` Word length, field of [Line Control register](LineControl).
    ///
    /// These bits indicate the number of data bits transmitted or received in a
    /// frame as follows:
    pub enum WordLength {
        /// b11 = 8 bits
        _8Bits = 0b11,
        /// b10 = 7 bits
        _7Bits = 0b10,
        /// b01 = 6 bits
        _6Bits = 0b01,
        /// b00 = 5 bits.
        _5Bits = 0b00,
    }

    /// Control Register, `UARTCR`
    ///
    /// The `UARTCR` register is the control register. All the bits are cleared
    /// to `0` on reset except for bits `9` and `8` that are set to `1`.
    ///
    /// # Source
    /// ARM DDI 0183G, 3.3.8 Control Register, `UARTCR`, Table 3-12
    #[bitsize(32)]
    #[doc(alias = "UARTCR")]
    #[derive(Clone, Copy, DebugBits, FromBits)]
    pub struct Control {
        /// `UARTEN` UART enable: 0 = UART is disabled. If the UART is disabled
        /// in the middle of transmission or reception, it completes the current
        /// character before stopping. 1 = the UART is enabled. Data
        /// transmission and reception occurs for either UART signals or SIR
        /// signals depending on the setting of the SIREN bit.
        pub enable_uart: bool,
        /// `SIREN` `SIR` enable: 0 = `IrDA` SIR ENDEC is disabled. `nSIROUT`
        /// remains LOW (no light pulse generated), and signal transitions on
        /// SIRIN have no effect. 1 = `IrDA` SIR ENDEC is enabled. Data is
        /// transmitted and received on nSIROUT and SIRIN. UARTTXD remains HIGH,
        /// in the marking state. Signal transitions on UARTRXD or modem status
        /// inputs have no effect. This bit has no effect if the UARTEN bit
        /// disables the UART.
        pub enable_sir: bool,
        /// `SIRLP` SIR low-power `IrDA` mode. This bit selects the `IrDA`
        /// encoding mode. If this bit is cleared to 0, low-level bits
        /// are transmitted as an active high pulse with a width of 3/
        /// 16th of the bit period. If this bit is set to 1, low-level
        /// bits are transmitted with a pulse width that is 3 times the
        /// period of the `IrLPBaud16` input signal, regardless of the
        /// selected bit rate. Setting this bit uses less power, but
        /// might reduce transmission distances.
        pub sir_lowpower_irda_mode: u1,
        /// Reserved, do not modify, read as zero.
        _reserved_zero_no_modify: u4,
        /// `LBE` Loopback enable. If this bit is set to 1 and the SIREN bit is
        /// set to 1 and the SIRTEST bit in the Test Control register, UARTTCR
        /// on page 4-5 is set to 1, then the nSIROUT path is inverted, and fed
        /// through to the SIRIN path. The SIRTEST bit in the test register must
        /// be set to 1 to override the normal half-duplex SIR operation. This
        /// must be the requirement for accessing the test registers during
        /// normal operation, and SIRTEST must be cleared to 0 when loopback
        /// testing is finished. This feature reduces the amount of external
        /// coupling required during system test. If this bit is set to 1, and
        /// the SIRTEST bit is set to 0, the UARTTXD path is fed through to the
        /// UARTRXD path. In either SIR mode or UART mode, when this bit is set,
        /// the modem outputs are also fed through to the modem inputs. This bit
        /// is cleared to 0 on reset, to disable loopback.
        pub enable_loopback: bool,
        /// `TXE` Transmit enable. If this bit is set to 1, the transmit section
        /// of the UART is enabled. Data transmission occurs for either UART
        /// signals, or SIR signals depending on the setting of the SIREN bit.
        /// When the UART is disabled in the middle of transmission, it
        /// completes the current character before stopping.
        pub enable_transmit: bool,
        /// `RXE` Receive enable. If this bit is set to 1, the receive section
        /// of the UART is enabled. Data reception occurs for either UART
        /// signals or SIR signals depending on the setting of the SIREN bit.
        /// When the UART is disabled in the middle of reception, it completes
        /// the current character before stopping.
        pub enable_receive: bool,
        /// `DTR` Data transmit ready. This bit is the complement of the UART
        /// data transmit ready, `nUARTDTR`, modem status output. That is, when
        /// the bit is programmed to a 1 then `nUARTDTR` is LOW.
        pub data_transmit_ready: bool,
        /// `RTS` Request to send. This bit is the complement of the UART
        /// request to send, `nUARTRTS`, modem status output. That is, when the
        /// bit is programmed to a 1 then `nUARTRTS` is LOW.
        pub request_to_send: bool,
        /// `Out1` This bit is the complement of the UART Out1 (`nUARTOut1`)
        /// modem status output. That is, when the bit is programmed to a 1 the
        /// output is 0. For DTE this can be used as Data Carrier Detect (DCD).
        pub out_1: bool,
        /// `Out2` This bit is the complement of the UART Out2 (`nUARTOut2`)
        /// modem status output. That is, when the bit is programmed to a 1, the
        /// output is 0. For DTE this can be used as Ring Indicator (RI).
        pub out_2: bool,
        /// `RTSEn` RTS hardware flow control enable. If this bit is set to 1,
        /// RTS hardware flow control is enabled. Data is only requested when
        /// there is space in the receive FIFO for it to be received.
        pub rts_hardware_flow_control_enable: bool,
        /// `CTSEn` CTS hardware flow control enable. If this bit is set to 1,
        /// CTS hardware flow control is enabled. Data is only transmitted when
        /// the `nUARTCTS` signal is asserted.
        pub cts_hardware_flow_control_enable: bool,
        /// 31:16 - Reserved, do not modify, read as zero.
        _reserved_zero_no_modify2: u16,
    }

    impl Control {
        pub fn reset(&mut self) {
            *self = 0.into();
            self.set_enable_receive(true);
            self.set_enable_transmit(true);
        }
    }

    impl Default for Control {
        fn default() -> Self {
            let mut ret: Self = 0.into();
            ret.reset();
            ret
        }
    }

    /// Interrupt status bits in UARTRIS, UARTMIS, UARTIMSC
    pub struct Interrupt(pub u32);

    impl Interrupt {
        pub const OE: Self = Self(1 << 10);
        pub const BE: Self = Self(1 << 9);
        pub const PE: Self = Self(1 << 8);
        pub const FE: Self = Self(1 << 7);
        pub const RT: Self = Self(1 << 6);
        pub const TX: Self = Self(1 << 5);
        pub const RX: Self = Self(1 << 4);
        pub const DSR: Self = Self(1 << 3);
        pub const DCD: Self = Self(1 << 2);
        pub const CTS: Self = Self(1 << 1);
        pub const RI: Self = Self(1 << 0);

        pub const E: Self = Self(Self::OE.0 | Self::BE.0 | Self::PE.0 | Self::FE.0);
        pub const MS: Self = Self(Self::RI.0 | Self::DSR.0 | Self::DCD.0 | Self::CTS.0);
    }
}
