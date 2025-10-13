// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::{
    collections::BTreeMap,
    ffi::{CStr, CString},
};

use serde_derive::{Deserialize, Serialize};
use serde_json;

use crate::{
    exceptions::AccessDescriptor,
    memory::{mmu::ResolvedAddress, AccessType, Address},
};

const SYSCALLS: &str = include_str!("./syscalls.json");

#[derive(Serialize, Deserialize, Clone, Debug, PartialEq, Eq)]
pub struct Syscall {
    esoteric: bool,
    index: u64,
    name: String,
    number: u64,
    signature: Vec<String>,
}

#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct Syscalls {
    entries: BTreeMap<u64, Syscall>,
}

fn print_char_buf(machine: &crate::machine::Armv8AMachine, addr: u64) -> Option<CString> {
    let accessdesc = AccessDescriptor {
        read: true,
        ..AccessDescriptor::new(true, &machine.cpu_state.PSTATE(), AccessType::GPR)
    };
    let ResolvedAddress {
        mem_region,
        address_inside_region,
        physical: _,
    } = machine
        .translate_address(Address(addr), Address(addr), false, accessdesc)
        .ok()?;
    let mmapped_region = mem_region.as_mmap()?;
    let r: &[u8] = &mmapped_region.as_ref()[address_inside_region.try_into().unwrap()..];
    let max_bytes = 1048;
    let r = &r[..max_bytes.min(r.len())];
    CStr::from_bytes_until_nul(r).ok().map(|c| c.into())
}

impl Syscalls {
    pub fn trace_syscall(machine: &crate::machine::Armv8AMachine) -> String {
        let v: serde_json::Value = serde_json::from_str(SYSCALLS).unwrap();

        let table: Vec<Syscall> = serde_json::from_value(v["syscalls"].clone()).unwrap();
        let table: BTreeMap<u64, Syscall> = table.into_iter().map(|v| (v.number, v)).collect();
        let syscall = &table[&machine.cpu_state.registers.x8];
        let args = [
            machine.cpu_state.registers.x0,
            machine.cpu_state.registers.x1,
            machine.cpu_state.registers.x2,
            machine.cpu_state.registers.x3,
            machine.cpu_state.registers.x4,
            machine.cpu_state.registers.x5,
        ]
        .into_iter()
        .zip(&syscall.signature)
        .map(|(reg, name)| {
            if name.contains("char *") {
                print_char_buf(machine, reg).map_or_else(
                    || format!("{name}: {reg:#x}"),
                    |buf| format!("{name}: {buf:?}"),
                )
            } else {
                format!("{name}: {reg:#x}")
            }
        })
        .collect::<Vec<String>>();
        format!("{}({})", syscall.name, args.join(", "))
    }
}

#[test]
fn test_syscall() {
    let v: serde_json::Value = serde_json::from_str(SYSCALLS).unwrap();

    let table: Vec<Syscall> = serde_json::from_value(v["syscalls"].clone()).unwrap();
    let table: BTreeMap<u64, Syscall> = table.into_iter().map(|v| (v.number, v)).collect();
    let syscall = &table[&0xdd];
    assert_eq!(&syscall.name, "execve");
}
