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

use simulans::jit;

use std::borrow::Cow;

mod samples {
    #![allow(dead_code)]

    /// ```text
    /// 0x40080000: sub sp, sp, #0x10
    /// 0x40080004: str w0, [sp, #0xc]
    /// 0x40080008: ldr w8, [sp, #0xc]
    /// 0x4008000c: ldr w9, [sp, #0xc]
    /// 0x40080010: mul w0, w8, w9
    /// 0x40080014: add sp, sp, #0x10
    /// 0x40080018: ret
    /// ```
    pub const SQUARED: &[u8] = b"\xff\x43\x00\xd1\xe0\x0f\x00\xb9\xe8\x0f\x40\xb9\xe9\x0f\x40\xb9\x00\x7d\x09\x1b\xff\x43\x00\x91\xc0\x03\x5f\xd6";
    /// ```text
    /// 1000: str   x0, [sp, #-16]! ; "\xe0\x0f\x1f\xf8"
    /// 1004: ldr   x0, [sp], #16   ; "\xe0\x07\x41\xf8"
    /// ```
    pub const LOAD_STORES: &[u8] = b"\xe0\x0f\x1f\xf8\xe0\x07\x41\xf8";

    /// ```text
    /// 0x40080000: mov x0, #0x1234
    /// 0x40080004: str x0, [sp, #-0x10]!
    /// 0x40080008: ldr x1, [sp], #0x10
    /// 0x4008000c: add x0, x0, x1
    /// ```
    pub const STACK_ADD: &[u8] =
        b"\x80\x46\x82\xd2\xe0\x0f\x1f\xf8\xe1\x07\x41\xf8\x00\x00\x01\x8b";
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = std::env::args_os().collect::<Vec<_>>();
    let input = match args.len() {
        0 | 1 => Cow::Borrowed(samples::SQUARED),
        2 => Cow::Owned(std::fs::read(&args[1])?),
        more => {
            eprintln!("Error: at most one argument is expected, but got {more}");
            std::process::exit(1);
        }
    };
    // Create the JIT instance, which manages all generated functions and data.
    let mut jit = jit::JIT::default();

    disas(&input)?;
    println!("sp_el0 = 0x{:x}", run_aarch64(&mut jit, &input)?);
    println!("cpu state after running is {:#?}", &jit.cpu_state);
    Ok(())
}

fn run_aarch64(jit: &mut jit::JIT, input: &[u8]) -> Result<i64, Box<dyn std::error::Error>> {
    let ret: i64 = unsafe { run_code(jit, input, ())? };
    Ok(ret)
}

/// Dissassembles and prints each decoded aarch64 instruction using Capstone library, for
/// debugging.
fn disas(input: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
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
    println!("Capstone output:");
    for insn in decoded_iter.as_ref() {
        println!("{}", insn);
    }
    Ok(())
}

/// Executes the given aarch64 binary code using the cranelift JIT compiler.
///
/// Feeds the given input into the JIT compiled function and returns the resulting output.
///
/// # Safety
///
/// This function is unsafe since it relies on the caller to provide it with the correct
/// input and output types. Using incorrect types at this point may corrupt the program's state.
unsafe fn run_code<I, O>(
    jit: &mut jit::JIT,
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
