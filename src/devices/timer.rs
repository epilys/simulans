// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Generic timer

// timer interrupts, architecturally defined
// const ARCH_TIMER_NS_EL2_IRQ: u16 = 26;
// const ARCH_TIMER_NS_EL2_VIRT_IRQ: u16 = 28;
// const ARCH_TIMER_S_EL1_IRQ: u16 = 29;
const ARCH_TIMER_NS_EL1_IRQ: u16 = 30;
const ARCH_TIMER_VIRT_IRQ: u16 = 27;

use std::sync::{
    atomic::{AtomicI32, AtomicU64, Ordering},
    mpsc::TrySendError,
    Arc,
};

use crate::{
    get_bits,
    machine::{
        interrupts::{InterruptRequest, Interrupts},
        Armv8AMachine,
    },
    set_bits,
};

#[repr(u8)]
#[allow(non_camel_case_types)]
pub enum RegisterID {
    CNTP_CTL_EL0 = 0,
    CNTP_TVAL_EL0,
    CNTP_CVAL_EL0,
    CNTV_CTL_EL0,
    CNTV_TVAL_EL0,
    CNTV_CVAL_EL0,
    CNTPCT_EL0,
    CNTVCT_EL0,
    CNTFRQ_EL0,
}

pub extern "C" fn timer_register_write(machine: &Armv8AMachine, register: RegisterID, value: u64) {
    match register {
        RegisterID::CNTP_CTL_EL0 => {
            machine.timer.cntp_ctl_el0.store(value, Ordering::Release);
        }
        RegisterID::CNTP_TVAL_EL0 => {
            machine
                .timer
                .cntp_tval_el0
                .store(value.try_into().unwrap_or(i32::MAX), Ordering::Release);
            let value = value + machine.timer.cntpct_el0.load(Ordering::SeqCst);
            machine.timer.cntp_cval_el0.store(value, Ordering::Release);
        }
        RegisterID::CNTP_CVAL_EL0 => {
            machine.timer.cntp_cval_el0.store(value, Ordering::Release);
        }
        RegisterID::CNTV_CTL_EL0 => {
            machine.timer.cntv_ctl_el0.store(value, Ordering::Release);
        }
        RegisterID::CNTV_TVAL_EL0 => {
            machine
                .timer
                .cntv_tval_el0
                .store(value.try_into().unwrap_or(i32::MAX), Ordering::Release);
            let value = value + machine.timer.cntpct_el0.load(Ordering::SeqCst);
            machine.timer.cntv_cval_el0.store(value, Ordering::Release);
        }
        RegisterID::CNTV_CVAL_EL0 => {
            machine.timer.cntv_cval_el0.store(value, Ordering::Release);
        }
        RegisterID::CNTFRQ_EL0 | RegisterID::CNTVCT_EL0 | RegisterID::CNTPCT_EL0 => {}
    }
}

pub extern "C" fn timer_register_read(machine: &Armv8AMachine, register: RegisterID) -> u64 {
    match register {
        RegisterID::CNTFRQ_EL0 => machine.timer.frq,
        RegisterID::CNTP_CTL_EL0 => machine.timer.cntp_ctl_el0.load(Ordering::SeqCst),
        RegisterID::CNTP_TVAL_EL0 => machine
            .timer
            .cntp_tval_el0
            .load(Ordering::Acquire)
            .cast_unsigned()
            .into(),
        RegisterID::CNTP_CVAL_EL0 => machine.timer.cntp_cval_el0.load(Ordering::SeqCst),
        RegisterID::CNTV_CTL_EL0 => machine.timer.cntv_ctl_el0.load(Ordering::SeqCst),
        RegisterID::CNTV_TVAL_EL0 => machine
            .timer
            .cntv_tval_el0
            .load(Ordering::Acquire)
            .cast_unsigned()
            .into(),
        RegisterID::CNTV_CVAL_EL0 => machine.timer.cntv_cval_el0.load(Ordering::SeqCst),
        RegisterID::CNTVCT_EL0 | RegisterID::CNTPCT_EL0 => {
            machine.timer.cntpct_el0.load(Ordering::SeqCst)
        }
    }
}

#[derive(Debug)]
#[allow(clippy::struct_field_names)]
pub struct GenericTimer {
    frq: u64,
    cntp_ctl_el0: Arc<AtomicU64>,
    cntp_cval_el0: Arc<AtomicU64>,
    cntp_tval_el0: Arc<AtomicI32>,
    cntpct_el0: Arc<AtomicU64>,
    cntv_ctl_el0: Arc<AtomicU64>,
    cntv_cval_el0: Arc<AtomicU64>,
    cntv_tval_el0: Arc<AtomicI32>,
}

impl GenericTimer {
    pub fn new(interrupts: &Interrupts) -> Self {
        let frq = 1_000_000_000;
        let generator = interrupts.generator.clone();
        let cntp_ctl_el0 = Arc::new(AtomicU64::new(0));
        let cntp_cval_el0 = Arc::new(AtomicU64::new(0));
        let cntp_tval_el0 = Arc::new(AtomicI32::new(0));
        let cntpct_el0 = Arc::new(AtomicU64::new(0));
        let cntv_ctl_el0 = Arc::new(AtomicU64::new(0));
        let cntv_cval_el0 = Arc::new(AtomicU64::new(0));
        let cntv_tval_el0 = Arc::new(AtomicI32::new(0));
        std::thread::Builder::new()
            .name("timer".into())
            .spawn({
                let cntpct_el0 = Arc::clone(&cntpct_el0);

                let cntp_ctl_el0 = Arc::clone(&cntp_ctl_el0);
                let cntp_cval_el0 = Arc::clone(&cntp_cval_el0);
                let cntp_tval_el0 = Arc::clone(&cntp_tval_el0);
                let cntv_ctl_el0 = Arc::clone(&cntv_ctl_el0);
                let cntv_cval_el0 = Arc::clone(&cntv_cval_el0);
                let cntv_tval_el0 = Arc::clone(&cntv_tval_el0);

                let adjust: u64 = 1_000_000;

                let sleep_dur = std::time::Duration::from_micros(1000);
                move || {
                    loop {
                        std::thread::sleep(sleep_dur);

                        let cntpct_val = cntpct_el0.fetch_add(adjust, Ordering::SeqCst) + adjust;
                        cntv_tval_el0.fetch_sub(adjust as i32, Ordering::SeqCst);
                        cntp_tval_el0.fetch_sub(adjust as i32, Ordering::SeqCst);

                        {
                            // physical timer

                            let mut cntp_ctl_val = cntp_ctl_el0.load(Ordering::Acquire);
                            let enabled = get_bits!(cntp_ctl_val, off = 0, len = 1) == 1;
                            let imask = get_bits!(cntp_ctl_val, off = 1, len = 1) == 1;

                            let cntp_cval = cntp_cval_el0.load(Ordering::Acquire);

                            let signal = if enabled {
                                // Timer Condition Met: CVAL <= System Count
                                let condition_met = cntp_cval <= cntpct_val;
                                while let Err(current_value) = cntp_ctl_el0.compare_exchange(
                                    cntp_ctl_val,
                                    set_bits!(
                                        cntp_ctl_val,
                                        off = 2,
                                        len = 1,
                                        val = u64::from(condition_met)
                                    ),
                                    Ordering::Acquire,
                                    Ordering::Relaxed,
                                ) {
                                    cntp_ctl_val = current_value;
                                }
                                condition_met && !imask
                            } else {
                                false
                            };
                            // signal interrupt
                            if matches!(
                                generator.irq_sender.try_send(InterruptRequest {
                                    interrupt_id: ARCH_TIMER_NS_EL1_IRQ,
                                    cpu_id: None,
                                    signal,
                                }),
                                Err(TrySendError::Disconnected(_))
                            ) {
                                break;
                            }
                        }
                        {
                            // virtual timer

                            let mut cntv_ctl_val = cntv_ctl_el0.load(Ordering::Acquire);
                            let enabled = get_bits!(cntv_ctl_val, off = 0, len = 1) == 1;
                            let imask = get_bits!(cntv_ctl_val, off = 1, len = 1) == 1;

                            let cntv_cval = cntv_cval_el0.load(Ordering::Acquire);

                            let signal = if enabled {
                                // Timer Condition Met: CVAL <= System Count
                                let condition_met = cntv_cval <= cntpct_val;
                                while let Err(current_value) = cntv_ctl_el0.compare_exchange(
                                    cntv_ctl_val,
                                    set_bits!(
                                        cntv_ctl_val,
                                        off = 2,
                                        len = 1,
                                        val = u64::from(condition_met)
                                    ),
                                    Ordering::Acquire,
                                    Ordering::Relaxed,
                                ) {
                                    cntv_ctl_val = current_value;
                                }
                                condition_met && !imask
                            } else {
                                false
                            };
                            if matches!(
                                generator.irq_sender.try_send(InterruptRequest {
                                    interrupt_id: ARCH_TIMER_VIRT_IRQ,
                                    cpu_id: None,
                                    signal,
                                }),
                                Err(TrySendError::Disconnected(_))
                            ) {
                                break;
                            }
                        }
                    }
                }
            })
            .unwrap();
        Self {
            frq,
            cntp_ctl_el0,
            cntp_cval_el0,
            cntp_tval_el0,
            cntv_ctl_el0,
            cntv_cval_el0,
            cntv_tval_el0,
            cntpct_el0,
        }
    }
}
