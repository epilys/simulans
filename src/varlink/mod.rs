//
// simulans
//
// Copyright 2025 Emmanouil Pitsidianakis <manos@pitsidianak.is>
//
// This file is part of simulans.
//
// simulans is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// simulans is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with simulans. If not, see <http://www.gnu.org/licenses/>.
//
// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later

#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(dead_code, unused_variables)]

pub mod com_github_epilys_simulans;
use std::io::BufRead;

use com_github_epilys_simulans::*;

pub struct VarlinkEndpoint {}

impl VarlinkInterface for VarlinkEndpoint {
    fn get_disassembly(
        &self,
        call: &mut dyn Call_GetDisassembly,
        r#address: Option<i64>,
        r#length: i64,
    ) -> varlink::Result<()> {
        Ok(())
    }

    fn get_generic_registers(
        &self,
        call: &mut dyn Call_GetGenericRegisters,
    ) -> varlink::Result<()> {
        Ok(())
    }
    fn get_machine_properties(
        &self,
        call: &mut dyn Call_GetMachineProperties,
    ) -> varlink::Result<()> {
        Ok(())
    }
    fn get_memory_range_value(
        &self,
        call: &mut dyn Call_GetMemoryRangeValue,
        r#address: i64,
        r#length: i64,
    ) -> varlink::Result<()> {
        Ok(())
    }
    fn get_memory_value(
        &self,
        call: &mut dyn Call_GetMemoryValue,
        r#address: i64,
    ) -> varlink::Result<()> {
        Ok(())
    }
    fn get_register(&self, call: &mut dyn Call_GetRegister, r#name: String) -> varlink::Result<()> {
        Ok(())
    }
    fn get_system_registers(&self, call: &mut dyn Call_GetSystemRegisters) -> varlink::Result<()> {
        Ok(())
    }
    fn step_i(&self, call: &mut dyn Call_StepI) -> varlink::Result<()> {
        Ok(())
    }
    fn call_upgraded(
        &self,
        _call: &mut varlink::Call,
        _bufreader: &mut dyn BufRead,
    ) -> varlink::Result<Vec<u8>> {
        Ok(Vec::new())
    }
}

pub fn create_varlink_endpoint() -> std::result::Result<(), Box<dyn std::error::Error>> {
    let endpoint = VarlinkEndpoint {};
    let interface = com_github_epilys_simulans::new(Box::new(endpoint));
    let service = ::varlink::VarlinkService::new(
        "com.github.epilys.simulans",
        "simulans debugger",
        "0.1",
        "http://github.com/epilys/simulans",
        vec![Box::new(interface)],
    );

    ::varlink::listen(
        service,
        "tcp:127.0.0.1:12345",
        &::varlink::ListenConfig {
            idle_timeout: 60 * 5,
            // stop_listening: Some(stop_listening),
            ..Default::default()
        },
    )?;
    Ok(())
}
