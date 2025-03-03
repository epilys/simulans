//
// simulans
//
// Copyright 2025- Manos Pitsidianakis
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

pub mod cpu_state;
pub mod jit;

/// Dissassembles and prints each decoded aarch64 instruction to stdout using Capstone library, for
/// debugging.
pub fn disas(input: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    use capstone::prelude::*;

    let mut cs = Capstone::new()
        .arm64()
        .mode(capstone::arch::arm64::ArchMode::Arm)
        .endian(capstone::Endian::Little)
        .detail(true)
        .build()
        .expect("Failed to create Capstone object");
    cs.set_syntax(capstone::Syntax::Intel)?;
    let decoded_iter = cs.disasm_all(input, 0x40080000)?;
    log::debug!("Capstone output:");
    for insn in decoded_iter.as_ref() {
        log::debug!("{}", insn);
    }
    Ok(())
}

/// Executes the given aarch64 binary code.
///
/// Feeds the given input into the JIT compiled function and returns the resulting output.
///
/// # Safety
///
/// This function is unsafe since it relies on the caller to provide it with the correct
/// input and output types. Using incorrect types at this point may corrupt the program's state.
pub unsafe fn run_code<I, O>(
    jit: &mut jit::Armv8AMachine,
    code: &[u8],
    input: I,
) -> Result<O, Box<dyn std::error::Error>> {
    // Pass the string to the JIT, and it returns a raw pointer to machine code.
    let code_ptr = jit.compile(code)?;
    // Cast the raw pointer to a typed function pointer. This is unsafe, because
    // this is the critical point where you have to trust that the generated code
    // is safe to be called.
    let code_fn = std::mem::transmute::<*const u8, fn(I) -> O>(code_ptr);
    // And now we can call it!
    Ok(code_fn(input))
}
