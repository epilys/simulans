//
// ____
//
// Copyright 2025 Emmanouil Pitsidianakis <manos@pitsidianak.is>
//
// This file is part of ____.
//
// ____ is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// ____ is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with ____. If not, see <http://www.gnu.org/licenses/>.
//
// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later

use capstone::prelude::*;
use core::mem;
use cranelift_jit_demo::jit;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Create the JIT instance, which manages all generated functions and data.
    let mut jit = jit::JIT::default();
    let input = b"\xe0\x0f\x1f\xf8\xe0\x07\x41\xf8";
    // 1000: str   x0, [sp, #-16]! ; "\xe0\x0f\x1f\xf8"
    // 1004: ldr   x0, [sp], #16   ; "\xe0\x07\x41\xf8"
    disas(input)?;
    run_aarch64(&mut jit, input)?;
    Ok(())
}

fn run_aarch64(jit: &mut jit::JIT, input: &[u8]) -> Result<isize, Box<dyn std::error::Error>> {
    unsafe { run_code(jit, input, ())? }
    Ok(0)
}

//fn run_aarch64(jit: &mut jit::JIT, input: &[u8]) -> Result<isize, Box<dyn std::error::Error>> {
//    // 1000: str   x0, [sp, #-16]! ; "\xe0\x0f\x1f\xf8"
//    // 1004: ldr   x0, [sp], #16   ; "\xe0\x07\x41\xf8"
//    let mut decoded_iter = bad64::disasm(input, 0x40080000);

//    let push = decoded_iter.next().unwrap().unwrap();

//    // check out the push
//    assert_eq!(push.address(), 0x1000);
//    assert_eq!(push.operands().len(), 2);
//    assert_eq!(push.op(), bad64::Op::STR);
//    assert_eq!(
//        push.operands()[0],
//        bad64::Operand::Reg {
//            reg: bad64::Reg::X0,
//            arrspec: None
//        }
//    );
//    assert_eq!(
//        push.operands()[1],
//        bad64::Operand::MemPreIdx {
//            reg: bad64::Reg::SP,
//            imm: bad64::Imm::Signed(-16)
//        }
//    );
//    assert_eq!(push.operands().get(2), None);

//    let pop = decoded_iter.next().unwrap().unwrap();

//    // check out the pop
//    assert_eq!(pop.address(), 0x1004);
//    assert_eq!(pop.operands().len(), 2);
//    assert_eq!(pop.op(), bad64::Op::LDR);
//    assert_eq!(
//        pop.operands().get(0),
//        Some(&bad64::Operand::Reg {
//            reg: bad64::Reg::X0,
//            arrspec: None
//        })
//    );
//    assert_eq!(
//        pop.operands().get(1),
//        Some(&bad64::Operand::MemPostIdxImm {
//            reg: bad64::Reg::SP,
//            imm: bad64::Imm::Signed(16)
//        })
//    );
//    assert_eq!(pop.operands().get(2), None);

//    // make sure there's nothing left
//    assert_eq!(decoded_iter.next(), None);
//    //jit.create_data("hello_string", "hello world!\0".as_bytes().to_vec())?;
//    //unsafe { run_code(jit, HELLO_CODE, ()) }
//    Ok(0)
//}

fn disas(input: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
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

/// Executes the given code using the cranelift JIT compiler.
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
    let code_fn = mem::transmute::<_, fn(I) -> O>(code_ptr);
    // And now we can call it!
    Ok(code_fn(input))
}
