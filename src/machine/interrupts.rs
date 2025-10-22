// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Interrupt handling

use std::{
    collections::BTreeMap,
    sync::mpsc::{channel, sync_channel, Receiver, Sender, SyncSender},
};

#[derive(Copy, Clone, Debug)]
pub struct InterruptRequest {
    pub interrupt_id: u16,
    pub cpu_id: Option<u8>,
    pub signal: bool,
}

#[derive(Debug, Clone)]
pub struct InterruptGenerator {
    pub irq_sender: SyncSender<InterruptRequest>,
}

pub struct Interrupts {
    pub generator: InterruptGenerator,
    generator_rcv: Receiver<InterruptRequest>,
    subscribers: BTreeMap<u64, Box<dyn Fn(InterruptRequest) + Send + Sync>>,
    fiq_rcv: Receiver<u8>,
    irq_rcv: Receiver<u8>,
    fiq_sender: FiqSignal,
    irq_sender: IrqSignal,
}

#[derive(Debug, Clone)]
pub struct FiqSignal {
    sender: Sender<u8>,
}

impl FiqSignal {
    pub fn send(&self, cpu_id: u8) {
        self.sender.send(cpu_id).unwrap();
    }
}

#[derive(Debug, Clone)]
pub struct IrqSignal {
    sender: Sender<u8>,
}

impl IrqSignal {
    pub fn send(&self, cpu_id: u8) {
        self.sender.send(cpu_id).unwrap();
    }
}

impl Interrupts {
    pub fn new() -> Self {
        let (irq_sender, generator_rcv) = sync_channel(1024 * 1024);
        let generator = InterruptGenerator { irq_sender };
        let (sender, fiq_rcv) = channel();
        let fiq_sender = FiqSignal { sender };
        let (sender, irq_rcv) = channel();
        let irq_sender = IrqSignal { sender };
        Self {
            generator,
            generator_rcv,
            subscribers: BTreeMap::default(),
            fiq_rcv,
            irq_rcv,
            fiq_sender,
            irq_sender,
        }
    }

    /// Receive and route any interrupts
    pub fn rcv(&self) -> bool {
        let mut any = false;

        while let Ok(irq) = self.generator_rcv.try_recv() {
            for sub in self.subscribers.values() {
                (sub)(irq);
            }

            any = true;
        }
        any
    }

    /// Update FIQ signal
    pub fn fiq(&self) -> bool {
        let mut any = false;

        while self.fiq_rcv.try_recv().is_ok() {
            any = true;
        }
        any
    }

    pub fn fiq_signal(&self) -> FiqSignal {
        self.fiq_sender.clone()
    }

    /// Update IRQ signal
    pub fn irq(&self) -> bool {
        let mut any = false;

        while self.irq_rcv.try_recv().is_ok() {
            any = true;
        }
        any
    }

    pub fn irq_signal(&self) -> IrqSignal {
        self.irq_sender.clone()
    }

    pub fn subscribe(
        &mut self,
        device_id: u64,
        handler: Box<dyn Fn(InterruptRequest) + Send + Sync>,
    ) {
        // FIXME: what about overridden values?
        self.subscribers.insert(device_id, handler);
    }
}

impl Default for Interrupts {
    fn default() -> Self {
        Self::new()
    }
}
