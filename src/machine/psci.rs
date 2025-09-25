// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Power State Coordination Interface handler

#![allow(non_camel_case_types)]

use crate::{cpu_state::ExitRequest, machine::Armv8AMachine};

#[repr(u32)]
enum FunctionId {
    /// `PSCI_VERSION`
    PSCIVersion = 0x8400_0000,
    /// `CPU_SUSPEND`
    CPUSuspend = 0x8400_0001,
    /// `CPU_SUSPEND_64`
    CPUSuspend64 = 0xC400_0001,
    /// `CPU_OFF`
    CPUOff = 0x8400_0002,
    /// `CPU_ON`
    CPUOn = 0x8400_0003,
    /// `CPU_ON_64`
    CPUOn64 = 0xC400_0003,
    /// `AFFINITY_INFO`
    AffinityInfo = 0x8400_0004,
    /// `AFFINITY_INFO_64`
    AffinityInfo64 = 0xC400_0004,
    /// `SYSTEM_OFF`
    SystemOff = 0x8400_0008,
    /// `SYSTEM_RESET`
    SystemReset = 0x8400_0009,
    /// `SYSTEM_RESET2`
    SystemReset2 = 0x8400_0012,
    /// `SYSTEM_RESET2_64`
    SystemReset264 = 0xC400_0012,
    /// `PSCI_FEATURES`
    PSCIFeatures = 0x8400_000A,
    /// `UNKNOWN`
    Unknown = 0xFFFFFFFF,
}

impl From<u64> for FunctionId {
    fn from(val: u64) -> Self {
        match val {
            v if v == Self::PSCIVersion as u64 => Self::PSCIVersion,
            v if v == Self::CPUSuspend as u64 => Self::CPUSuspend,
            v if v == Self::CPUSuspend64 as u64 => Self::CPUSuspend64,
            v if v == Self::CPUOff as u64 => Self::CPUOff,
            v if v == Self::CPUOn as u64 => Self::CPUOn,
            v if v == Self::CPUOn64 as u64 => Self::CPUOn64,
            v if v == Self::AffinityInfo as u64 => Self::AffinityInfo,
            v if v == Self::AffinityInfo64 as u64 => Self::AffinityInfo64,
            v if v == Self::SystemOff as u64 => Self::SystemOff,
            v if v == Self::SystemReset as u64 => Self::SystemReset,
            v if v == Self::SystemReset2 as u64 => Self::SystemReset2,
            v if v == Self::SystemReset264 as u64 => Self::SystemReset264,
            v if v == Self::PSCIFeatures as u64 => Self::PSCIFeatures,
            _ => Self::Unknown,
        }
    }
}

#[allow(dead_code)]
#[repr(i32)]
enum ReturnCode {
    /// `SUCCESS`
    Success = 0,
    /// `NOT_SUPPORTED`
    NotSupported = -1,
    /// `INVALID_PARAMETERS`
    InvalidParameters = -2,
    /// `DENIED`
    Denied = -3,
    /// `ALREADY_ON`
    AlreadyOn = -4,
    /// `ON_PENDING`
    OnPending = -5,
    /// `INTERNAL_FAILURE`
    InternalFailure = -6,
    /// `NOT_PRESENT`
    NotPresent = -7,
    /// `DISABLED`
    Disabled = -8,
    /// `INVALID_ADDRESS`
    InvalidAddress = -9,
}

impl Armv8AMachine {
    /// Returns `true` if the call was handled as a PSCI call.
    pub fn psci_call(&mut self, immediate: u16) -> bool {
        if immediate != 0 {
            return false;
        }
        let function_id = FunctionId::from(self.cpu_state.registers.x0);
        match function_id {
            FunctionId::Unknown => {
                self.cpu_state.registers.x0 = function_id as u64;
            }
            FunctionId::PSCIVersion => {
                // Bits[31:16] Major Version Bits[15:0] Minor Version
                self.cpu_state.registers.x0 = 1 << 16 | 1;
            }
            FunctionId::PSCIFeatures => {
                let psci_func_id = FunctionId::from(self.cpu_state.registers.x1);
                self.cpu_state.registers.x0 = if matches!(psci_func_id, FunctionId::Unknown) {
                    ReturnCode::NotSupported as u64
                } else {
                    ReturnCode::Success as u64
                };
            }
            FunctionId::SystemOff => {
                *self.cpu_state.exit_request.lock().unwrap() = Some(ExitRequest::Poweroff);
            }
            FunctionId::SystemReset => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::SystemReset2 => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::SystemReset264 => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::CPUSuspend => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::CPUSuspend64 => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::CPUOn => {
                self.cpu_state.registers.x0 = ReturnCode::AlreadyOn as u64;
            }
            FunctionId::CPUOn64 => {
                self.cpu_state.registers.x0 = ReturnCode::AlreadyOn as u64;
            }
            FunctionId::CPUOff => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::AffinityInfo => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
            FunctionId::AffinityInfo64 => {
                self.cpu_state.registers.x0 = ReturnCode::NotSupported as u64;
            }
        }
        true
    }
}
