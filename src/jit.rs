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

use crate::frontend::*;
use capstone::prelude::*;
use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, Linkage, Module};
use indexmap::IndexMap;
use std::slice;

macro_rules! I64 {
    () => {{
        cranelift::prelude::Type::int(64).expect("Could not create I64 type")
    }};
}

struct Stack {
    //data: Box<[u8; 1_000_000 * 4096]>,
    data: Box<[u8; 100 * 4096]>,
    offset: usize,
}

impl Stack {
    fn addr_as_value(&self, offset: usize, builder: &mut FunctionBuilder<'_>) -> Value {
        assert!(offset < self.data.as_slice().len(), "offset was {offset}");
        builder.ins().iconst(
            I64! {},
            i64::try_from(unsafe { self.data.as_ptr().add(self.offset) }.addr()).unwrap(),
        )
    }
}

/// The basic JIT class.
pub struct JIT {
    /// The function builder context, which is reused across multiple
    /// FunctionBuilder instances.
    builder_context: FunctionBuilderContext,

    /// The main Cranelift context, which holds the state for codegen. Cranelift
    /// separates this from `Module` to allow for parallel compilation, with a
    /// context per thread, though this isn't in the simple demo here.
    ctx: codegen::Context,

    /// The data description, which is to data objects what `ctx` is to functions.
    data_description: DataDescription,
    stack: Stack,

    /// The module, with the jit backend, which manages the JIT'd
    /// functions.
    module: JITModule,
}

impl Default for JIT {
    fn default() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        let stack_vec = vec![0; 100 * 4096];
        let ptr = Box::into_raw(stack_vec.into_boxed_slice()) as *mut [u8; 100 * 4096];

        // SAFETY: The underlying array of a slice has the exact same layout as an actual array `[T; N]` if `N` is equal to the slice's length.
        let stack_data = unsafe { Box::from_raw(ptr) };
        let offset = stack_data.as_slice().len();
        let stack = Stack {
            data: stack_data,
            offset,
        };

        let module = JITModule::new(builder);
        Self {
            builder_context: FunctionBuilderContext::new(),
            ctx: module.make_context(),
            data_description: DataDescription::new(),
            stack,
            module,
        }
    }
}

impl JIT {
    /// Compile a string in the toy language into machine code.
    pub fn compile(&mut self, input: &[u8]) -> Result<*const u8, Box<dyn std::error::Error>> {
        // translate the input into Cranelift IR.
        self.translate(input)?;

        // Next, declare the function to jit. Functions must be declared
        // before they can be called, or defined.
        //
        // TODO: This may be an area where the API should be streamlined; should
        // we have a version of `declare_function` that automatically declares
        // the function?
        let id = self
            .module
            .declare_function("jit", Linkage::Export, &self.ctx.func.signature)
            .map_err(|e| e.to_string())?;

        // Define the function to jit. This finishes compilation, although
        // there may be outstanding relocations to perform. Currently, jit
        // cannot finish relocations until all functions to be called are
        // defined. For this toy demo for now, we'll just finalize the
        // function below.
        self.module
            .define_function(id, &mut self.ctx)
            .map_err(|e| e.to_string())?;

        // Now that compilation is finished, we can clear out the context state.
        self.module.clear_context(&mut self.ctx);

        // Finalize the functions which we just defined, which resolves any
        // outstanding relocations (patching in addresses, now that they're
        // available).
        self.module.finalize_definitions().unwrap();

        // We can now retrieve a pointer to the machine code.
        let code = self.module.get_finalized_function(id);

        Ok(code)
    }

    /// Create a zero-initialized data section.
    pub fn create_data(
        &mut self,
        name: &str,
        contents: Vec<u8>,
    ) -> Result<&[u8], Box<dyn std::error::Error>> {
        // The steps here are analogous to `compile`, except that data is much
        // simpler than functions.
        self.data_description.define(contents.into_boxed_slice());
        let id = self
            .module
            .declare_data(name, Linkage::Export, true, false)
            .map_err(|e| e.to_string())?;

        self.module
            .define_data(id, &self.data_description)
            .map_err(|e| e.to_string())?;
        self.data_description.clear();
        self.module.finalize_definitions().unwrap();
        let buffer = self.module.get_finalized_data(id);
        // TODO: Can we move the unsafe into cranelift?
        Ok(unsafe { slice::from_raw_parts(buffer.0, buffer.1) })
    }

    // Translate from toy-language AST nodes into Cranelift IR.
    fn translate(&mut self, input: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        let decoded_iter = bad64::disasm(input, 0x40080000);

        // Return type of JIT code
        let int = cranelift::prelude::Type::int(64).expect("Could not create I64 type");

        // for _p in &params {
        //     self.ctx.func.signature.params.push(AbiParam::new(int));
        // }

        // Our toy language currently only supports one return value, though
        // Cranelift is designed to support more.
        self.ctx.func.signature.returns.push(AbiParam::new(int));

        // Create the builder to build a function.
        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);

        // Create the entry block, to start emitting code in.
        let entry_block = builder.create_block();

        // Since this is the entry block, add block parameters corresponding to
        // the function's parameters.
        //
        // TODO: Streamline the API here.
        builder.append_block_params_for_function_params(entry_block);

        // Tell the builder to emit code in this block.
        builder.switch_to_block(entry_block);

        // And, tell the builder that this block will have no further
        // predecessors. Since it's the entry block, it won't have any
        // predecessors.
        builder.seal_block(entry_block);

        // // The toy language allows variables to be declared implicitly.
        // // Walk the AST and declare all implicitly-declared variables.
        // let variables =
        //     declare_variables(int, &mut builder, &params, &the_return, &stmts, entry_block);

        let mut variables = IndexMap::new();
        let zero = builder.ins().iconst(int, 0);
        let return_variable = declare_variable(int, &mut builder, &mut variables, bad64::Reg::X0);
        builder.def_var(return_variable, zero);
        // Now translate the statements of the function body.
        let mut trans = FunctionTranslator {
            int,
            builder,
            variables,
            stack: &mut self.stack,
            module: &mut self.module,
        };
        for insn in decoded_iter {
            let insn = insn.map_err(|err| err.to_string())?;
            println!("{:#?}", insn);
            println!("{}", insn);
            trans.translate_instruction(insn);
        }

        // Set up the return variable of the function. Above, we declared a
        // variable to hold the return value. Here, we just do a use of that
        // variable.
        let return_variable = trans.variables.get(&bad64::Reg::X0).unwrap();
        let return_value = trans.builder.use_var(*return_variable);

        // Emit the return instruction.
        trans.builder.ins().return_(&[return_value]);

        // Tell the builder we're done with this function.
        trans.builder.finalize();
        Ok(())
    }
}

/// A collection of state used for translating from toy-language AST nodes
/// into Cranelift IR.
struct FunctionTranslator<'a> {
    int: types::Type,
    builder: FunctionBuilder<'a>,
    variables: IndexMap<bad64::Reg, Variable>,
    stack: &'a mut Stack,
    module: &'a mut JITModule,
}

impl<'a> FunctionTranslator<'a> {
    // /// When you write out instructions in Cranelift, you get back `Value`s. You
    // /// can then use these references in other instructions.
    // fn translate_expr(&mut self, expr: Expr) -> Value {
    //     match expr {
    //         Expr::Literal(literal) => {
    //             let imm: i32 = literal.parse().unwrap();
    //             self.builder.ins().iconst(self.int, i64::from(imm))
    //         }

    //         Expr::Add(lhs, rhs) => {
    //             let lhs = self.translate_expr(*lhs);
    //             let rhs = self.translate_expr(*rhs);
    //             self.builder.ins().iadd(lhs, rhs)
    //         }

    //         Expr::Sub(lhs, rhs) => {
    //             let lhs = self.translate_expr(*lhs);
    //             let rhs = self.translate_expr(*rhs);
    //             self.builder.ins().isub(lhs, rhs)
    //         }

    //         Expr::Mul(lhs, rhs) => {
    //             let lhs = self.translate_expr(*lhs);
    //             let rhs = self.translate_expr(*rhs);
    //             self.builder.ins().imul(lhs, rhs)
    //         }

    //         Expr::Div(lhs, rhs) => {
    //             let lhs = self.translate_expr(*lhs);
    //             let rhs = self.translate_expr(*rhs);
    //             self.builder.ins().udiv(lhs, rhs)
    //         }

    //         Expr::Eq(lhs, rhs) => self.translate_icmp(IntCC::Equal, *lhs, *rhs),
    //         Expr::Ne(lhs, rhs) => self.translate_icmp(IntCC::NotEqual, *lhs, *rhs),
    //         Expr::Lt(lhs, rhs) => self.translate_icmp(IntCC::SignedLessThan, *lhs, *rhs),
    //         Expr::Le(lhs, rhs) => self.translate_icmp(IntCC::SignedLessThanOrEqual, *lhs, *rhs),
    //         Expr::Gt(lhs, rhs) => self.translate_icmp(IntCC::SignedGreaterThan, *lhs, *rhs),
    //         Expr::Ge(lhs, rhs) => self.translate_icmp(IntCC::SignedGreaterThanOrEqual, *lhs, *rhs),
    //         Expr::Call(name, args) => self.translate_call(name, args),
    //         Expr::GlobalDataAddr(name) => self.translate_global_data_addr(name),
    //         Expr::Identifier(name) => {
    //             // `use_var` is used to read the value of a variable.
    //             let variable = self.variables.get(&name).expect("variable not defined");
    //             self.builder.use_var(*variable)
    //         }
    //         Expr::Assign(name, expr) => self.translate_assign(name, *expr),
    //         Expr::IfElse(condition, then_body, else_body) => {
    //             self.translate_if_else(*condition, then_body, else_body)
    //         }
    //         Expr::WhileLoop(condition, loop_body) => {
    //             self.translate_while_loop(*condition, loop_body)
    //         }
    //     }
    // }

    // fn translate_assign(&mut self, name: String, expr: Expr) -> Value {
    //     // `def_var` is used to write the value of a variable. Note that
    //     // variables can have multiple definitions. Cranelift will
    //     // convert them into SSA form for itself automatically.
    //     let new_value = self.translate_expr(expr);
    //     let variable = self.variables.get(&name).unwrap();
    //     self.builder.def_var(*variable, new_value);
    //     new_value
    // }

    // fn translate_icmp(&mut self, cmp: IntCC, lhs: Expr, rhs: Expr) -> Value {
    //     let lhs = self.translate_expr(lhs);
    //     let rhs = self.translate_expr(rhs);
    //     self.builder.ins().icmp(cmp, lhs, rhs)
    // }

    // fn translate_if_else(
    //     &mut self,
    //     condition: Expr,
    //     then_body: Vec<Expr>,
    //     else_body: Vec<Expr>,
    // ) -> Value {
    //     let condition_value = self.translate_expr(condition);

    //     let then_block = self.builder.create_block();
    //     let else_block = self.builder.create_block();
    //     let merge_block = self.builder.create_block();

    //     // If-else constructs in the toy language have a return value.
    //     // In traditional SSA form, this would produce a PHI between
    //     // the then and else bodies. Cranelift uses block parameters,
    //     // so set up a parameter in the merge block, and we'll pass
    //     // the return values to it from the branches.
    //     self.builder.append_block_param(merge_block, self.int);

    //     // Test the if condition and conditionally branch.
    //     self.builder
    //         .ins()
    //         .brif(condition_value, then_block, &[], else_block, &[]);

    //     self.builder.switch_to_block(then_block);
    //     self.builder.seal_block(then_block);
    //     let mut then_return = self.builder.ins().iconst(self.int, 0);
    //     for expr in then_body {
    //         then_return = self.translate_expr(expr);
    //     }

    //     // Jump to the merge block, passing it the block return value.
    //     self.builder.ins().jump(merge_block, &[then_return]);

    //     self.builder.switch_to_block(else_block);
    //     self.builder.seal_block(else_block);
    //     let mut else_return = self.builder.ins().iconst(self.int, 0);
    //     for expr in else_body {
    //         else_return = self.translate_expr(expr);
    //     }

    //     // Jump to the merge block, passing it the block return value.
    //     self.builder.ins().jump(merge_block, &[else_return]);

    //     // Switch to the merge block for subsequent statements.
    //     self.builder.switch_to_block(merge_block);

    //     // We've now seen all the predecessors of the merge block.
    //     self.builder.seal_block(merge_block);

    //     // Read the value of the if-else by reading the merge block
    //     // parameter.
    //     let phi = self.builder.block_params(merge_block)[0];

    //     phi
    // }

    // fn translate_while_loop(&mut self, condition: Expr, loop_body: Vec<Expr>) -> Value {
    //     let header_block = self.builder.create_block();
    //     let body_block = self.builder.create_block();
    //     let exit_block = self.builder.create_block();

    //     self.builder.ins().jump(header_block, &[]);
    //     self.builder.switch_to_block(header_block);

    //     let condition_value = self.translate_expr(condition);
    //     self.builder
    //         .ins()
    //         .brif(condition_value, body_block, &[], exit_block, &[]);

    //     self.builder.switch_to_block(body_block);
    //     self.builder.seal_block(body_block);

    //     for expr in loop_body {
    //         self.translate_expr(expr);
    //     }
    //     self.builder.ins().jump(header_block, &[]);

    //     self.builder.switch_to_block(exit_block);

    //     // We've reached the bottom of the loop, so there will be no
    //     // more backedges to the header to exits to the bottom.
    //     self.builder.seal_block(header_block);
    //     self.builder.seal_block(exit_block);

    //     // Just return 0 for now.
    //     self.builder.ins().iconst(self.int, 0)
    // }

    // fn translate_call(&mut self, name: String, args: Vec<Expr>) -> Value {
    //     let mut sig = self.module.make_signature();

    //     // Add a parameter for each argument.
    //     for _arg in &args {
    //         sig.params.push(AbiParam::new(self.int));
    //     }

    //     // For simplicity for now, just make all calls return a single I64.
    //     sig.returns.push(AbiParam::new(self.int));

    //     // TODO: Streamline the API here?
    //     let callee = self
    //         .module
    //         .declare_function(&name, Linkage::Import, &sig)
    //         .expect("problem declaring function");
    //     let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

    //     let mut arg_values = Vec::new();
    //     for arg in args {
    //         arg_values.push(self.translate_expr(arg))
    //     }
    //     let call = self.builder.ins().call(local_callee, &arg_values);
    //     self.builder.inst_results(call)[0]
    // }

    // fn translate_global_data_addr(&mut self, name: String) -> Value {
    //     let sym = self
    //         .module
    //         .declare_data(&name, Linkage::Export, true, false)
    //         .expect("problem declaring data object");
    //     let local_id = self.module.declare_data_in_func(sym, self.builder.func);

    //     let pointer = self.module.target_config().pointer_type();
    //     self.builder.ins().symbol_value(pointer, local_id)
    // }

    fn reg_to_var(&mut self, reg: &bad64::Reg) -> Value {
        let Some(var) = self.variables.get(reg) else {
            let var = Variable::new(self.variables.len());
            self.variables.insert(*reg, var);
            let zero = self.builder.ins().iconst(self.int, 0);
            self.builder.def_var(var, zero);
            //self.builder.declare_var(var, self.int);
            return self.builder.use_var(var);
        };
        self.builder.use_var(*var)
    }

    fn translate_instruction(&mut self, instruction: bad64::Instruction) {
        use bad64::Op;

        match instruction.op() {
            Op::NOP => {}
            // Special registers
            Op::MSR => todo!(),
            Op::MRS => todo!(),
            // Memory-ops
            Op::ADRP => todo!(),
            Op::STR => {
                let value = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => self.reg_to_var(reg),
                    other => panic!("unexpected lhs in store: {:?}", other),
                };
                let (target, offset) = match instruction.operands()[1] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => {
                        let reg_target = self.reg_to_var(reg);
                        // FIXME ??? huh
                        self.builder.ins().store(
                            cranelift::prelude::MemFlags::new(),
                            value,
                            reg_target,
                            0,
                        );
                        return;
                    }
                    bad64::Operand::MemPreIdx {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Signed(imm),
                    } => {
                        // FIXME: pre-update SP
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (stack_ptr, imm)
                    }
                    bad64::Operand::MemPreIdx {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Unsigned(imm),
                    } => {
                        // FIXME: pre-update SP
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (
                            stack_ptr, imm as i64, // FIXME
                        )
                    }
                    bad64::Operand::MemPreIdx { ref reg, imm } => {
                        // FIXME: pre-update reg
                        let imm = match imm {
                            bad64::Imm::Unsigned(imm) => imm as i64, // FIXME
                            bad64::Imm::Signed(imm) => imm,
                        };
                        let var = self.reg_to_var(reg);
                        let addr = self.builder.ins().load(
                            cranelift::prelude::Type::int(64).unwrap(),
                            cranelift::prelude::MemFlags::new(),
                            var,
                            codegen::ir::immediates::Offset32::try_from_i64(imm).unwrap(),
                        );
                        (addr, 0)
                    }
                    bad64::Operand::MemPostIdxImm {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Signed(imm),
                    } => {
                        // FIXME; post-update SP value
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (stack_ptr, imm)
                    }
                    bad64::Operand::MemPostIdxImm {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Unsigned(imm),
                    } => {
                        // FIXME; post-update SP value
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (
                            stack_ptr, imm as i64, // FIXME
                        )
                    }
                    bad64::Operand::MemPostIdxImm { ref reg, imm } => {
                        // FIXME; post-update reg value
                        let imm = match imm {
                            bad64::Imm::Unsigned(imm) => imm as i64, // FIXME
                            bad64::Imm::Signed(imm) => imm,
                        };
                        let var = self.reg_to_var(reg);
                        let addr = self.builder.ins().load(
                            cranelift::prelude::Type::int(64).unwrap(),
                            cranelift::prelude::MemFlags::new(),
                            var,
                            codegen::ir::immediates::Offset32::try_from_i64(imm).unwrap(),
                        );
                        (addr, 0)
                    }
                    other => panic!("unexpected rhs in store: {:?}", other),
                };
                self.builder.ins().store(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    codegen::ir::immediates::Offset32::try_from_i64(offset).unwrap(),
                );
            }
            Op::LDR => {
                let target = match instruction.operands()[0] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => self.reg_to_var(reg),
                    other => panic!("unexpected lhs in load: {:?}", other),
                };
                let (source, offset) = match instruction.operands()[1] {
                    bad64::Operand::Reg {
                        ref reg,
                        arrspec: None,
                    } => {
                        let reg_target = self.reg_to_var(reg);
                        (reg_target, 0)
                    }
                    bad64::Operand::MemPreIdx {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Signed(imm),
                    } => {
                        // FIXME: pre-update SP
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (stack_ptr, imm)
                    }
                    bad64::Operand::MemPreIdx {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Unsigned(imm),
                    } => {
                        // FIXME: pre-update SP
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (
                            stack_ptr, imm as i64, // FIXME
                        )
                    }
                    bad64::Operand::MemPreIdx { ref reg, imm } => {
                        // FIXME: pre-update reg
                        let imm = match imm {
                            bad64::Imm::Unsigned(imm) => imm as i64, // FIXME
                            bad64::Imm::Signed(imm) => imm,
                        };
                        let var = self.reg_to_var(reg);
                        let addr = self.builder.ins().load(
                            cranelift::prelude::Type::int(64).unwrap(),
                            cranelift::prelude::MemFlags::new(),
                            var,
                            codegen::ir::immediates::Offset32::try_from_i64(imm).unwrap(),
                        );
                        (addr, 0)
                    }
                    bad64::Operand::MemPostIdxImm {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Signed(imm),
                    } => {
                        // FIXME; post-update SP value
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (stack_ptr, imm)
                    }
                    bad64::Operand::MemPostIdxImm {
                        reg: bad64::Reg::SP,
                        imm: bad64::Imm::Unsigned(imm),
                    } => {
                        // FIXME; post-update SP value
                        let stack_offset = todo!();
                        let stack_ptr = self.stack.addr_as_value(stack_offset, &mut self.builder);
                        (
                            stack_ptr, imm as i64, // FIXME
                        )
                    }
                    bad64::Operand::MemPostIdxImm { ref reg, imm } => {
                        // FIXME; post-update reg value
                        let imm = match imm {
                            bad64::Imm::Unsigned(imm) => imm as i64, // FIXME
                            bad64::Imm::Signed(imm) => imm,
                        };
                        let var = self.reg_to_var(reg);
                        let addr = self.builder.ins().load(
                            cranelift::prelude::Type::int(64).unwrap(),
                            cranelift::prelude::MemFlags::new(),
                            var,
                            codegen::ir::immediates::Offset32::try_from_i64(imm).unwrap(),
                        );
                        (addr, 0)
                    }
                    other => panic!("unexpected rhs in store: {:?}", other),
                };
                let value = self.builder.ins().load(
                    cranelift::prelude::Type::int(64).unwrap(),
                    cranelift::prelude::MemFlags::new(),
                    source,
                    codegen::ir::immediates::Offset32::try_from_i64(offset).unwrap(),
                );
                self.builder.ins().store(
                    cranelift::prelude::MemFlags::new(),
                    value,
                    target,
                    codegen::ir::immediates::Offset32::try_from_i64(offset).unwrap(),
                );
            }
            // Moves
            Op::MOV => todo!(),
            Op::MOVK => todo!(),
            Op::MOVZ => todo!(),
            // Int-ops
            Op::ADD => todo!(),
            Op::SUB => todo!(),
            Op::MUL => todo!(),
            // Branches
            Op::BR => todo!(),
            Op::BFI => todo!(),
            Op::RET => todo!(),
            // Bit-ops
            Op::AND => todo!(),

            // rest
            Op::ABS => todo!(),
            Op::ADC => todo!(),
            Op::ADCLB => todo!(),
            Op::ADCLT => todo!(),
            Op::ADCS => todo!(),
            Op::ADDG => todo!(),
            Op::ADDHA => todo!(),
            Op::ADDHN => todo!(),
            Op::ADDHN2 => todo!(),
            Op::ADDHNB => todo!(),
            Op::ADDHNT => todo!(),
            Op::ADDP => todo!(),
            Op::ADDPL => todo!(),
            Op::ADDS => todo!(),
            Op::ADDV => todo!(),
            Op::ADDVA => todo!(),
            Op::ADDVL => todo!(),
            Op::ADR => todo!(),
            Op::AESD => todo!(),
            Op::AESE => todo!(),
            Op::AESIMC => todo!(),
            Op::AESMC => todo!(),
            Op::ANDS => todo!(),
            Op::ANDV => todo!(),
            Op::ASR => todo!(),
            Op::ASRD => todo!(),
            Op::ASRR => todo!(),
            Op::ASRV => todo!(),
            Op::AT => todo!(),
            Op::AUTDA => todo!(),
            Op::AUTDB => todo!(),
            Op::AUTDZA => todo!(),
            Op::AUTDZB => todo!(),
            Op::AUTIA => todo!(),
            Op::AUTIA1716 => todo!(),
            Op::AUTIASP => todo!(),
            Op::AUTIAZ => todo!(),
            Op::AUTIB => todo!(),
            Op::AUTIB1716 => todo!(),
            Op::AUTIBSP => todo!(),
            Op::AUTIBZ => todo!(),
            Op::AUTIZA => todo!(),
            Op::AUTIZB => todo!(),
            Op::AXFLAG => todo!(),
            Op::B => todo!(),
            Op::BCAX => todo!(),
            Op::BDEP => todo!(),
            Op::BEXT => todo!(),
            Op::BFC => todo!(),
            Op::BFCVT => todo!(),
            Op::BFCVTN => todo!(),
            Op::BFCVTN2 => todo!(),
            Op::BFCVTNT => todo!(),
            Op::BFDOT => todo!(),
            Op::BFM => todo!(),
            Op::BFMLAL => todo!(),
            Op::BFMLALB => todo!(),
            Op::BFMLALT => todo!(),
            Op::BFMMLA => todo!(),
            Op::BFMOPA => todo!(),
            Op::BFMOPS => todo!(),
            Op::BFXIL => todo!(),
            Op::BGRP => todo!(),
            Op::BIC => todo!(),
            Op::BICS => todo!(),
            Op::BIF => todo!(),
            Op::BIT => todo!(),
            Op::BL => todo!(),
            Op::BLR => todo!(),
            Op::BLRAA => todo!(),
            Op::BLRAAZ => todo!(),
            Op::BLRAB => todo!(),
            Op::BLRABZ => todo!(),
            Op::BRAA => todo!(),
            Op::BRAAZ => todo!(),
            Op::BRAB => todo!(),
            Op::BRABZ => todo!(),
            Op::BRK => todo!(),
            Op::BRKA => todo!(),
            Op::BRKAS => todo!(),
            Op::BRKB => todo!(),
            Op::BRKBS => todo!(),
            Op::BRKN => todo!(),
            Op::BRKNS => todo!(),
            Op::BRKPA => todo!(),
            Op::BRKPAS => todo!(),
            Op::BRKPB => todo!(),
            Op::BRKPBS => todo!(),
            Op::BSL => todo!(),
            Op::BSL1N => todo!(),
            Op::BSL2N => todo!(),
            Op::BTI => todo!(),
            Op::B_AL => todo!(),
            Op::B_CC => todo!(),
            Op::B_CS => todo!(),
            Op::B_EQ => todo!(),
            Op::B_GE => todo!(),
            Op::B_GT => todo!(),
            Op::B_HI => todo!(),
            Op::B_LE => todo!(),
            Op::B_LS => todo!(),
            Op::B_LT => todo!(),
            Op::B_MI => todo!(),
            Op::B_NE => todo!(),
            Op::B_NV => todo!(),
            Op::B_PL => todo!(),
            Op::B_VC => todo!(),
            Op::B_VS => todo!(),
            Op::CADD => todo!(),
            Op::CAS => todo!(),
            Op::CASA => todo!(),
            Op::CASAB => todo!(),
            Op::CASAH => todo!(),
            Op::CASAL => todo!(),
            Op::CASALB => todo!(),
            Op::CASALH => todo!(),
            Op::CASB => todo!(),
            Op::CASH => todo!(),
            Op::CASL => todo!(),
            Op::CASLB => todo!(),
            Op::CASLH => todo!(),
            Op::CASP => todo!(),
            Op::CASPA => todo!(),
            Op::CASPAL => todo!(),
            Op::CASPL => todo!(),
            Op::CBNZ => todo!(),
            Op::CBZ => todo!(),
            Op::CCMN => todo!(),
            Op::CCMP => todo!(),
            Op::CDOT => todo!(),
            Op::CFINV => todo!(),
            Op::CFP => todo!(),
            Op::CINC => todo!(),
            Op::CINV => todo!(),
            Op::CLASTA => todo!(),
            Op::CLASTB => todo!(),
            Op::CLREX => todo!(),
            Op::CLS => todo!(),
            Op::CLZ => todo!(),
            Op::CMEQ => todo!(),
            Op::CMGE => todo!(),
            Op::CMGT => todo!(),
            Op::CMHI => todo!(),
            Op::CMHS => todo!(),
            Op::CMLA => todo!(),
            Op::CMLE => todo!(),
            Op::CMLT => todo!(),
            Op::CMN => todo!(),
            Op::CMP => todo!(),
            Op::CMPEQ => todo!(),
            Op::CMPGE => todo!(),
            Op::CMPGT => todo!(),
            Op::CMPHI => todo!(),
            Op::CMPHS => todo!(),
            Op::CMPLE => todo!(),
            Op::CMPLO => todo!(),
            Op::CMPLS => todo!(),
            Op::CMPLT => todo!(),
            Op::CMPNE => todo!(),
            Op::CMPP => todo!(),
            Op::CMTST => todo!(),
            Op::CNEG => todo!(),
            Op::CNOT => todo!(),
            Op::CNT => todo!(),
            Op::CNTB => todo!(),
            Op::CNTD => todo!(),
            Op::CNTH => todo!(),
            Op::CNTP => todo!(),
            Op::CNTW => todo!(),
            Op::COMPACT => todo!(),
            Op::CPP => todo!(),
            Op::CPY => todo!(),
            Op::CRC32B => todo!(),
            Op::CRC32CB => todo!(),
            Op::CRC32CH => todo!(),
            Op::CRC32CW => todo!(),
            Op::CRC32CX => todo!(),
            Op::CRC32H => todo!(),
            Op::CRC32W => todo!(),
            Op::CRC32X => todo!(),
            Op::CSDB => todo!(),
            Op::CSEL => todo!(),
            Op::CSET => todo!(),
            Op::CSETM => todo!(),
            Op::CSINC => todo!(),
            Op::CSINV => todo!(),
            Op::CSNEG => todo!(),
            Op::CTERMEQ => todo!(),
            Op::CTERMNE => todo!(),
            Op::DC => todo!(),
            Op::DCPS1 => todo!(),
            Op::DCPS2 => todo!(),
            Op::DCPS3 => todo!(),
            Op::DECB => todo!(),
            Op::DECD => todo!(),
            Op::DECH => todo!(),
            Op::DECP => todo!(),
            Op::DECW => todo!(),
            Op::DGH => todo!(),
            Op::DMB => todo!(),
            Op::DRPS => todo!(),
            Op::DSB => todo!(),
            Op::DUP => todo!(),
            Op::DUPM => todo!(),
            Op::DVP => todo!(),
            Op::EON => todo!(),
            Op::EOR => todo!(),
            Op::EOR3 => todo!(),
            Op::EORBT => todo!(),
            Op::EORS => todo!(),
            Op::EORTB => todo!(),
            Op::EORV => todo!(),
            Op::ERET => todo!(),
            Op::ERETAA => todo!(),
            Op::ERETAB => todo!(),
            Op::ESB => todo!(),
            Op::EXT => todo!(),
            Op::EXTR => todo!(),
            Op::FABD => todo!(),
            Op::FABS => todo!(),
            Op::FACGE => todo!(),
            Op::FACGT => todo!(),
            Op::FACLE => todo!(),
            Op::FACLT => todo!(),
            Op::FADD => todo!(),
            Op::FADDA => todo!(),
            Op::FADDP => todo!(),
            Op::FADDV => todo!(),
            Op::FCADD => todo!(),
            Op::FCCMP => todo!(),
            Op::FCCMPE => todo!(),
            Op::FCMEQ => todo!(),
            Op::FCMGE => todo!(),
            Op::FCMGT => todo!(),
            Op::FCMLA => todo!(),
            Op::FCMLE => todo!(),
            Op::FCMLT => todo!(),
            Op::FCMNE => todo!(),
            Op::FCMP => todo!(),
            Op::FCMPE => todo!(),
            Op::FCMUO => todo!(),
            Op::FCPY => todo!(),
            Op::FCSEL => todo!(),
            Op::FCVT => todo!(),
            Op::FCVTAS => todo!(),
            Op::FCVTAU => todo!(),
            Op::FCVTL => todo!(),
            Op::FCVTL2 => todo!(),
            Op::FCVTLT => todo!(),
            Op::FCVTMS => todo!(),
            Op::FCVTMU => todo!(),
            Op::FCVTN => todo!(),
            Op::FCVTN2 => todo!(),
            Op::FCVTNS => todo!(),
            Op::FCVTNT => todo!(),
            Op::FCVTNU => todo!(),
            Op::FCVTPS => todo!(),
            Op::FCVTPU => todo!(),
            Op::FCVTX => todo!(),
            Op::FCVTXN => todo!(),
            Op::FCVTXN2 => todo!(),
            Op::FCVTXNT => todo!(),
            Op::FCVTZS => todo!(),
            Op::FCVTZU => todo!(),
            Op::FDIV => todo!(),
            Op::FDIVR => todo!(),
            Op::FDUP => todo!(),
            Op::FEXPA => todo!(),
            Op::FJCVTZS => todo!(),
            Op::FLOGB => todo!(),
            Op::FMAD => todo!(),
            Op::FMADD => todo!(),
            Op::FMAX => todo!(),
            Op::FMAXNM => todo!(),
            Op::FMAXNMP => todo!(),
            Op::FMAXNMV => todo!(),
            Op::FMAXP => todo!(),
            Op::FMAXV => todo!(),
            Op::FMIN => todo!(),
            Op::FMINNM => todo!(),
            Op::FMINNMP => todo!(),
            Op::FMINNMV => todo!(),
            Op::FMINP => todo!(),
            Op::FMINV => todo!(),
            Op::FMLA => todo!(),
            Op::FMLAL => todo!(),
            Op::FMLAL2 => todo!(),
            Op::FMLALB => todo!(),
            Op::FMLALT => todo!(),
            Op::FMLS => todo!(),
            Op::FMLSL => todo!(),
            Op::FMLSL2 => todo!(),
            Op::FMLSLB => todo!(),
            Op::FMLSLT => todo!(),
            Op::FMMLA => todo!(),
            Op::FMOPA => todo!(),
            Op::FMOPS => todo!(),
            Op::FMOV => todo!(),
            Op::FMSB => todo!(),
            Op::FMSUB => todo!(),
            Op::FMUL => todo!(),
            Op::FMULX => todo!(),
            Op::FNEG => todo!(),
            Op::FNMAD => todo!(),
            Op::FNMADD => todo!(),
            Op::FNMLA => todo!(),
            Op::FNMLS => todo!(),
            Op::FNMSB => todo!(),
            Op::FNMSUB => todo!(),
            Op::FNMUL => todo!(),
            Op::FRECPE => todo!(),
            Op::FRECPS => todo!(),
            Op::FRECPX => todo!(),
            Op::FRINT32X => todo!(),
            Op::FRINT32Z => todo!(),
            Op::FRINT64X => todo!(),
            Op::FRINT64Z => todo!(),
            Op::FRINTA => todo!(),
            Op::FRINTI => todo!(),
            Op::FRINTM => todo!(),
            Op::FRINTN => todo!(),
            Op::FRINTP => todo!(),
            Op::FRINTX => todo!(),
            Op::FRINTZ => todo!(),
            Op::FRSQRTE => todo!(),
            Op::FRSQRTS => todo!(),
            Op::FSCALE => todo!(),
            Op::FSQRT => todo!(),
            Op::FSUB => todo!(),
            Op::FSUBR => todo!(),
            Op::FTMAD => todo!(),
            Op::FTSMUL => todo!(),
            Op::FTSSEL => todo!(),
            Op::GMI => todo!(),
            Op::HINT => todo!(),
            Op::HISTCNT => todo!(),
            Op::HISTSEG => todo!(),
            Op::HLT => todo!(),
            Op::HVC => todo!(),
            Op::IC => todo!(),
            Op::INCB => todo!(),
            Op::INCD => todo!(),
            Op::INCH => todo!(),
            Op::INCP => todo!(),
            Op::INCW => todo!(),
            Op::INDEX => todo!(),
            Op::INS => todo!(),
            Op::INSR => todo!(),
            Op::IRG => todo!(),
            Op::ISB => todo!(),
            Op::LASTA => todo!(),
            Op::LASTB => todo!(),
            Op::LD1 => todo!(),
            Op::LD1B => todo!(),
            Op::LD1D => todo!(),
            Op::LD1H => todo!(),
            Op::LD1Q => todo!(),
            Op::LD1R => todo!(),
            Op::LD1RB => todo!(),
            Op::LD1RD => todo!(),
            Op::LD1RH => todo!(),
            Op::LD1ROB => todo!(),
            Op::LD1ROD => todo!(),
            Op::LD1ROH => todo!(),
            Op::LD1ROW => todo!(),
            Op::LD1RQB => todo!(),
            Op::LD1RQD => todo!(),
            Op::LD1RQH => todo!(),
            Op::LD1RQW => todo!(),
            Op::LD1RSB => todo!(),
            Op::LD1RSH => todo!(),
            Op::LD1RSW => todo!(),
            Op::LD1RW => todo!(),
            Op::LD1SB => todo!(),
            Op::LD1SH => todo!(),
            Op::LD1SW => todo!(),
            Op::LD1W => todo!(),
            Op::LD2 => todo!(),
            Op::LD2B => todo!(),
            Op::LD2D => todo!(),
            Op::LD2H => todo!(),
            Op::LD2R => todo!(),
            Op::LD2W => todo!(),
            Op::LD3 => todo!(),
            Op::LD3B => todo!(),
            Op::LD3D => todo!(),
            Op::LD3H => todo!(),
            Op::LD3R => todo!(),
            Op::LD3W => todo!(),
            Op::LD4 => todo!(),
            Op::LD4B => todo!(),
            Op::LD4D => todo!(),
            Op::LD4H => todo!(),
            Op::LD4R => todo!(),
            Op::LD4W => todo!(),
            Op::LD64B => todo!(),
            Op::LDADD => todo!(),
            Op::LDADDA => todo!(),
            Op::LDADDAB => todo!(),
            Op::LDADDAH => todo!(),
            Op::LDADDAL => todo!(),
            Op::LDADDALB => todo!(),
            Op::LDADDALH => todo!(),
            Op::LDADDB => todo!(),
            Op::LDADDH => todo!(),
            Op::LDADDL => todo!(),
            Op::LDADDLB => todo!(),
            Op::LDADDLH => todo!(),
            Op::LDAPR => todo!(),
            Op::LDAPRB => todo!(),
            Op::LDAPRH => todo!(),
            Op::LDAPUR => todo!(),
            Op::LDAPURB => todo!(),
            Op::LDAPURH => todo!(),
            Op::LDAPURSB => todo!(),
            Op::LDAPURSH => todo!(),
            Op::LDAPURSW => todo!(),
            Op::LDAR => todo!(),
            Op::LDARB => todo!(),
            Op::LDARH => todo!(),
            Op::LDAXP => todo!(),
            Op::LDAXR => todo!(),
            Op::LDAXRB => todo!(),
            Op::LDAXRH => todo!(),
            Op::LDCLR => todo!(),
            Op::LDCLRA => todo!(),
            Op::LDCLRAB => todo!(),
            Op::LDCLRAH => todo!(),
            Op::LDCLRAL => todo!(),
            Op::LDCLRALB => todo!(),
            Op::LDCLRALH => todo!(),
            Op::LDCLRB => todo!(),
            Op::LDCLRH => todo!(),
            Op::LDCLRL => todo!(),
            Op::LDCLRLB => todo!(),
            Op::LDCLRLH => todo!(),
            Op::LDEOR => todo!(),
            Op::LDEORA => todo!(),
            Op::LDEORAB => todo!(),
            Op::LDEORAH => todo!(),
            Op::LDEORAL => todo!(),
            Op::LDEORALB => todo!(),
            Op::LDEORALH => todo!(),
            Op::LDEORB => todo!(),
            Op::LDEORH => todo!(),
            Op::LDEORL => todo!(),
            Op::LDEORLB => todo!(),
            Op::LDEORLH => todo!(),
            Op::LDFF1B => todo!(),
            Op::LDFF1D => todo!(),
            Op::LDFF1H => todo!(),
            Op::LDFF1SB => todo!(),
            Op::LDFF1SH => todo!(),
            Op::LDFF1SW => todo!(),
            Op::LDFF1W => todo!(),
            Op::LDG => todo!(),
            Op::LDGM => todo!(),
            Op::LDLAR => todo!(),
            Op::LDLARB => todo!(),
            Op::LDLARH => todo!(),
            Op::LDNF1B => todo!(),
            Op::LDNF1D => todo!(),
            Op::LDNF1H => todo!(),
            Op::LDNF1SB => todo!(),
            Op::LDNF1SH => todo!(),
            Op::LDNF1SW => todo!(),
            Op::LDNF1W => todo!(),
            Op::LDNP => todo!(),
            Op::LDNT1B => todo!(),
            Op::LDNT1D => todo!(),
            Op::LDNT1H => todo!(),
            Op::LDNT1SB => todo!(),
            Op::LDNT1SH => todo!(),
            Op::LDNT1SW => todo!(),
            Op::LDNT1W => todo!(),
            Op::LDP => todo!(),
            Op::LDPSW => todo!(),
            Op::LDRAA => todo!(),
            Op::LDRAB => todo!(),
            Op::LDRB => todo!(),
            Op::LDRH => todo!(),
            Op::LDRSB => todo!(),
            Op::LDRSH => todo!(),
            Op::LDRSW => todo!(),
            Op::LDSET => todo!(),
            Op::LDSETA => todo!(),
            Op::LDSETAB => todo!(),
            Op::LDSETAH => todo!(),
            Op::LDSETAL => todo!(),
            Op::LDSETALB => todo!(),
            Op::LDSETALH => todo!(),
            Op::LDSETB => todo!(),
            Op::LDSETH => todo!(),
            Op::LDSETL => todo!(),
            Op::LDSETLB => todo!(),
            Op::LDSETLH => todo!(),
            Op::LDSMAX => todo!(),
            Op::LDSMAXA => todo!(),
            Op::LDSMAXAB => todo!(),
            Op::LDSMAXAH => todo!(),
            Op::LDSMAXAL => todo!(),
            Op::LDSMAXALB => todo!(),
            Op::LDSMAXALH => todo!(),
            Op::LDSMAXB => todo!(),
            Op::LDSMAXH => todo!(),
            Op::LDSMAXL => todo!(),
            Op::LDSMAXLB => todo!(),
            Op::LDSMAXLH => todo!(),
            Op::LDSMIN => todo!(),
            Op::LDSMINA => todo!(),
            Op::LDSMINAB => todo!(),
            Op::LDSMINAH => todo!(),
            Op::LDSMINAL => todo!(),
            Op::LDSMINALB => todo!(),
            Op::LDSMINALH => todo!(),
            Op::LDSMINB => todo!(),
            Op::LDSMINH => todo!(),
            Op::LDSMINL => todo!(),
            Op::LDSMINLB => todo!(),
            Op::LDSMINLH => todo!(),
            Op::LDTR => todo!(),
            Op::LDTRB => todo!(),
            Op::LDTRH => todo!(),
            Op::LDTRSB => todo!(),
            Op::LDTRSH => todo!(),
            Op::LDTRSW => todo!(),
            Op::LDUMAX => todo!(),
            Op::LDUMAXA => todo!(),
            Op::LDUMAXAB => todo!(),
            Op::LDUMAXAH => todo!(),
            Op::LDUMAXAL => todo!(),
            Op::LDUMAXALB => todo!(),
            Op::LDUMAXALH => todo!(),
            Op::LDUMAXB => todo!(),
            Op::LDUMAXH => todo!(),
            Op::LDUMAXL => todo!(),
            Op::LDUMAXLB => todo!(),
            Op::LDUMAXLH => todo!(),
            Op::LDUMIN => todo!(),
            Op::LDUMINA => todo!(),
            Op::LDUMINAB => todo!(),
            Op::LDUMINAH => todo!(),
            Op::LDUMINAL => todo!(),
            Op::LDUMINALB => todo!(),
            Op::LDUMINALH => todo!(),
            Op::LDUMINB => todo!(),
            Op::LDUMINH => todo!(),
            Op::LDUMINL => todo!(),
            Op::LDUMINLB => todo!(),
            Op::LDUMINLH => todo!(),
            Op::LDUR => todo!(),
            Op::LDURB => todo!(),
            Op::LDURH => todo!(),
            Op::LDURSB => todo!(),
            Op::LDURSH => todo!(),
            Op::LDURSW => todo!(),
            Op::LDXP => todo!(),
            Op::LDXR => todo!(),
            Op::LDXRB => todo!(),
            Op::LDXRH => todo!(),
            Op::LSL => todo!(),
            Op::LSLR => todo!(),
            Op::LSLV => todo!(),
            Op::LSR => todo!(),
            Op::LSRR => todo!(),
            Op::LSRV => todo!(),
            Op::MAD => todo!(),
            Op::MADD => todo!(),
            Op::MATCH => todo!(),
            Op::MLA => todo!(),
            Op::MLS => todo!(),
            Op::MNEG => todo!(),
            Op::MOVA => todo!(),
            Op::MOVI => todo!(),
            Op::MOVN => todo!(),
            Op::MOVPRFX => todo!(),
            Op::MOVS => todo!(),
            Op::MSB => todo!(),
            Op::MSUB => todo!(),
            Op::MVN => todo!(),
            Op::MVNI => todo!(),
            Op::NAND => todo!(),
            Op::NANDS => todo!(),
            Op::NBSL => todo!(),
            Op::NEG => todo!(),
            Op::NEGS => todo!(),
            Op::NGC => todo!(),
            Op::NGCS => todo!(),
            Op::NMATCH => todo!(),
            Op::NOR => todo!(),
            Op::NORS => todo!(),
            Op::NOT => todo!(),
            Op::NOTS => todo!(),
            Op::ORN => todo!(),
            Op::ORNS => todo!(),
            Op::ORR => todo!(),
            Op::ORRS => todo!(),
            Op::ORV => todo!(),
            Op::PACDA => todo!(),
            Op::PACDB => todo!(),
            Op::PACDZA => todo!(),
            Op::PACDZB => todo!(),
            Op::PACGA => todo!(),
            Op::PACIA => todo!(),
            Op::PACIA1716 => todo!(),
            Op::PACIASP => todo!(),
            Op::PACIAZ => todo!(),
            Op::PACIB => todo!(),
            Op::PACIB1716 => todo!(),
            Op::PACIBSP => todo!(),
            Op::PACIBZ => todo!(),
            Op::PACIZA => todo!(),
            Op::PACIZB => todo!(),
            Op::PFALSE => todo!(),
            Op::PFIRST => todo!(),
            Op::PMUL => todo!(),
            Op::PMULL => todo!(),
            Op::PMULL2 => todo!(),
            Op::PMULLB => todo!(),
            Op::PMULLT => todo!(),
            Op::PNEXT => todo!(),
            Op::PRFB => todo!(),
            Op::PRFD => todo!(),
            Op::PRFH => todo!(),
            Op::PRFM => todo!(),
            Op::PRFUM => todo!(),
            Op::PRFW => todo!(),
            Op::PSB => todo!(),
            Op::PSSBB => todo!(),
            Op::PTEST => todo!(),
            Op::PTRUE => todo!(),
            Op::PTRUES => todo!(),
            Op::PUNPKHI => todo!(),
            Op::PUNPKLO => todo!(),
            Op::RADDHN => todo!(),
            Op::RADDHN2 => todo!(),
            Op::RADDHNB => todo!(),
            Op::RADDHNT => todo!(),
            Op::RAX1 => todo!(),
            Op::RBIT => todo!(),
            Op::RDFFR => todo!(),
            Op::RDFFRS => todo!(),
            Op::RDVL => todo!(),
            Op::RETAA => todo!(),
            Op::RETAB => todo!(),
            Op::REV => todo!(),
            Op::REV16 => todo!(),
            Op::REV32 => todo!(),
            Op::REV64 => todo!(),
            Op::REVB => todo!(),
            Op::REVD => todo!(),
            Op::REVH => todo!(),
            Op::REVW => todo!(),
            Op::RMIF => todo!(),
            Op::ROR => todo!(),
            Op::RORV => todo!(),
            Op::RSHRN => todo!(),
            Op::RSHRN2 => todo!(),
            Op::RSHRNB => todo!(),
            Op::RSHRNT => todo!(),
            Op::RSUBHN => todo!(),
            Op::RSUBHN2 => todo!(),
            Op::RSUBHNB => todo!(),
            Op::RSUBHNT => todo!(),
            Op::SABA => todo!(),
            Op::SABAL => todo!(),
            Op::SABAL2 => todo!(),
            Op::SABALB => todo!(),
            Op::SABALT => todo!(),
            Op::SABD => todo!(),
            Op::SABDL => todo!(),
            Op::SABDL2 => todo!(),
            Op::SABDLB => todo!(),
            Op::SABDLT => todo!(),
            Op::SADALP => todo!(),
            Op::SADDL => todo!(),
            Op::SADDL2 => todo!(),
            Op::SADDLB => todo!(),
            Op::SADDLBT => todo!(),
            Op::SADDLP => todo!(),
            Op::SADDLT => todo!(),
            Op::SADDLV => todo!(),
            Op::SADDV => todo!(),
            Op::SADDW => todo!(),
            Op::SADDW2 => todo!(),
            Op::SADDWB => todo!(),
            Op::SADDWT => todo!(),
            Op::SB => todo!(),
            Op::SBC => todo!(),
            Op::SBCLB => todo!(),
            Op::SBCLT => todo!(),
            Op::SBCS => todo!(),
            Op::SBFIZ => todo!(),
            Op::SBFM => todo!(),
            Op::SBFX => todo!(),
            Op::SCLAMP => todo!(),
            Op::SCVTF => todo!(),
            Op::SDIV => todo!(),
            Op::SDIVR => todo!(),
            Op::SDOT => todo!(),
            Op::SEL => todo!(),
            Op::SETF16 => todo!(),
            Op::SETF8 => todo!(),
            Op::SETFFR => todo!(),
            Op::SEV => todo!(),
            Op::SEVL => todo!(),
            Op::SHA1C => todo!(),
            Op::SHA1H => todo!(),
            Op::SHA1M => todo!(),
            Op::SHA1P => todo!(),
            Op::SHA1SU0 => todo!(),
            Op::SHA1SU1 => todo!(),
            Op::SHA256H => todo!(),
            Op::SHA256H2 => todo!(),
            Op::SHA256SU0 => todo!(),
            Op::SHA256SU1 => todo!(),
            Op::SHA512H => todo!(),
            Op::SHA512H2 => todo!(),
            Op::SHA512SU0 => todo!(),
            Op::SHA512SU1 => todo!(),
            Op::SHADD => todo!(),
            Op::SHL => todo!(),
            Op::SHLL => todo!(),
            Op::SHLL2 => todo!(),
            Op::SHRN => todo!(),
            Op::SHRN2 => todo!(),
            Op::SHRNB => todo!(),
            Op::SHRNT => todo!(),
            Op::SHSUB => todo!(),
            Op::SHSUBR => todo!(),
            Op::SLI => todo!(),
            Op::SM3PARTW1 => todo!(),
            Op::SM3PARTW2 => todo!(),
            Op::SM3SS1 => todo!(),
            Op::SM3TT1A => todo!(),
            Op::SM3TT1B => todo!(),
            Op::SM3TT2A => todo!(),
            Op::SM3TT2B => todo!(),
            Op::SM4E => todo!(),
            Op::SM4EKEY => todo!(),
            Op::SMADDL => todo!(),
            Op::SMAX => todo!(),
            Op::SMAXP => todo!(),
            Op::SMAXV => todo!(),
            Op::SMC => todo!(),
            Op::SMIN => todo!(),
            Op::SMINP => todo!(),
            Op::SMINV => todo!(),
            Op::SMLAL => todo!(),
            Op::SMLAL2 => todo!(),
            Op::SMLALB => todo!(),
            Op::SMLALT => todo!(),
            Op::SMLSL => todo!(),
            Op::SMLSL2 => todo!(),
            Op::SMLSLB => todo!(),
            Op::SMLSLT => todo!(),
            Op::SMMLA => todo!(),
            Op::SMNEGL => todo!(),
            Op::SMOPA => todo!(),
            Op::SMOPS => todo!(),
            Op::SMOV => todo!(),
            Op::SMSTART => todo!(),
            Op::SMSTOP => todo!(),
            Op::SMSUBL => todo!(),
            Op::SMULH => todo!(),
            Op::SMULL => todo!(),
            Op::SMULL2 => todo!(),
            Op::SMULLB => todo!(),
            Op::SMULLT => todo!(),
            Op::SPLICE => todo!(),
            Op::SQABS => todo!(),
            Op::SQADD => todo!(),
            Op::SQCADD => todo!(),
            Op::SQDECB => todo!(),
            Op::SQDECD => todo!(),
            Op::SQDECH => todo!(),
            Op::SQDECP => todo!(),
            Op::SQDECW => todo!(),
            Op::SQDMLAL => todo!(),
            Op::SQDMLAL2 => todo!(),
            Op::SQDMLALB => todo!(),
            Op::SQDMLALBT => todo!(),
            Op::SQDMLALT => todo!(),
            Op::SQDMLSL => todo!(),
            Op::SQDMLSL2 => todo!(),
            Op::SQDMLSLB => todo!(),
            Op::SQDMLSLBT => todo!(),
            Op::SQDMLSLT => todo!(),
            Op::SQDMULH => todo!(),
            Op::SQDMULL => todo!(),
            Op::SQDMULL2 => todo!(),
            Op::SQDMULLB => todo!(),
            Op::SQDMULLT => todo!(),
            Op::SQINCB => todo!(),
            Op::SQINCD => todo!(),
            Op::SQINCH => todo!(),
            Op::SQINCP => todo!(),
            Op::SQINCW => todo!(),
            Op::SQNEG => todo!(),
            Op::SQRDCMLAH => todo!(),
            Op::SQRDMLAH => todo!(),
            Op::SQRDMLSH => todo!(),
            Op::SQRDMULH => todo!(),
            Op::SQRSHL => todo!(),
            Op::SQRSHLR => todo!(),
            Op::SQRSHRN => todo!(),
            Op::SQRSHRN2 => todo!(),
            Op::SQRSHRNB => todo!(),
            Op::SQRSHRNT => todo!(),
            Op::SQRSHRUN => todo!(),
            Op::SQRSHRUN2 => todo!(),
            Op::SQRSHRUNB => todo!(),
            Op::SQRSHRUNT => todo!(),
            Op::SQSHL => todo!(),
            Op::SQSHLR => todo!(),
            Op::SQSHLU => todo!(),
            Op::SQSHRN => todo!(),
            Op::SQSHRN2 => todo!(),
            Op::SQSHRNB => todo!(),
            Op::SQSHRNT => todo!(),
            Op::SQSHRUN => todo!(),
            Op::SQSHRUN2 => todo!(),
            Op::SQSHRUNB => todo!(),
            Op::SQSHRUNT => todo!(),
            Op::SQSUB => todo!(),
            Op::SQSUBR => todo!(),
            Op::SQXTN => todo!(),
            Op::SQXTN2 => todo!(),
            Op::SQXTNB => todo!(),
            Op::SQXTNT => todo!(),
            Op::SQXTUN => todo!(),
            Op::SQXTUN2 => todo!(),
            Op::SQXTUNB => todo!(),
            Op::SQXTUNT => todo!(),
            Op::SRHADD => todo!(),
            Op::SRI => todo!(),
            Op::SRSHL => todo!(),
            Op::SRSHLR => todo!(),
            Op::SRSHR => todo!(),
            Op::SRSRA => todo!(),
            Op::SSBB => todo!(),
            Op::SSHL => todo!(),
            Op::SSHLL => todo!(),
            Op::SSHLL2 => todo!(),
            Op::SSHLLB => todo!(),
            Op::SSHLLT => todo!(),
            Op::SSHR => todo!(),
            Op::SSRA => todo!(),
            Op::SSUBL => todo!(),
            Op::SSUBL2 => todo!(),
            Op::SSUBLB => todo!(),
            Op::SSUBLBT => todo!(),
            Op::SSUBLT => todo!(),
            Op::SSUBLTB => todo!(),
            Op::SSUBW => todo!(),
            Op::SSUBW2 => todo!(),
            Op::SSUBWB => todo!(),
            Op::SSUBWT => todo!(),
            Op::ST1 => todo!(),
            Op::ST1B => todo!(),
            Op::ST1D => todo!(),
            Op::ST1H => todo!(),
            Op::ST1Q => todo!(),
            Op::ST1W => todo!(),
            Op::ST2 => todo!(),
            Op::ST2B => todo!(),
            Op::ST2D => todo!(),
            Op::ST2G => todo!(),
            Op::ST2H => todo!(),
            Op::ST2W => todo!(),
            Op::ST3 => todo!(),
            Op::ST3B => todo!(),
            Op::ST3D => todo!(),
            Op::ST3H => todo!(),
            Op::ST3W => todo!(),
            Op::ST4 => todo!(),
            Op::ST4B => todo!(),
            Op::ST4D => todo!(),
            Op::ST4H => todo!(),
            Op::ST4W => todo!(),
            Op::ST64B => todo!(),
            Op::ST64BV => todo!(),
            Op::ST64BV0 => todo!(),
            Op::STADD => todo!(),
            Op::STADDB => todo!(),
            Op::STADDH => todo!(),
            Op::STADDL => todo!(),
            Op::STADDLB => todo!(),
            Op::STADDLH => todo!(),
            Op::STCLR => todo!(),
            Op::STCLRB => todo!(),
            Op::STCLRH => todo!(),
            Op::STCLRL => todo!(),
            Op::STCLRLB => todo!(),
            Op::STCLRLH => todo!(),
            Op::STEOR => todo!(),
            Op::STEORB => todo!(),
            Op::STEORH => todo!(),
            Op::STEORL => todo!(),
            Op::STEORLB => todo!(),
            Op::STEORLH => todo!(),
            Op::STG => todo!(),
            Op::STGM => todo!(),
            Op::STGP => todo!(),
            Op::STLLR => todo!(),
            Op::STLLRB => todo!(),
            Op::STLLRH => todo!(),
            Op::STLR => todo!(),
            Op::STLRB => todo!(),
            Op::STLRH => todo!(),
            Op::STLUR => todo!(),
            Op::STLURB => todo!(),
            Op::STLURH => todo!(),
            Op::STLXP => todo!(),
            Op::STLXR => todo!(),
            Op::STLXRB => todo!(),
            Op::STLXRH => todo!(),
            Op::STNP => todo!(),
            Op::STNT1B => todo!(),
            Op::STNT1D => todo!(),
            Op::STNT1H => todo!(),
            Op::STNT1W => todo!(),
            Op::STP => todo!(),
            Op::STRB => todo!(),
            Op::STRH => todo!(),
            Op::STSET => todo!(),
            Op::STSETB => todo!(),
            Op::STSETH => todo!(),
            Op::STSETL => todo!(),
            Op::STSETLB => todo!(),
            Op::STSETLH => todo!(),
            Op::STSMAX => todo!(),
            Op::STSMAXB => todo!(),
            Op::STSMAXH => todo!(),
            Op::STSMAXL => todo!(),
            Op::STSMAXLB => todo!(),
            Op::STSMAXLH => todo!(),
            Op::STSMIN => todo!(),
            Op::STSMINB => todo!(),
            Op::STSMINH => todo!(),
            Op::STSMINL => todo!(),
            Op::STSMINLB => todo!(),
            Op::STSMINLH => todo!(),
            Op::STTR => todo!(),
            Op::STTRB => todo!(),
            Op::STTRH => todo!(),
            Op::STUMAX => todo!(),
            Op::STUMAXB => todo!(),
            Op::STUMAXH => todo!(),
            Op::STUMAXL => todo!(),
            Op::STUMAXLB => todo!(),
            Op::STUMAXLH => todo!(),
            Op::STUMIN => todo!(),
            Op::STUMINB => todo!(),
            Op::STUMINH => todo!(),
            Op::STUMINL => todo!(),
            Op::STUMINLB => todo!(),
            Op::STUMINLH => todo!(),
            Op::STUR => todo!(),
            Op::STURB => todo!(),
            Op::STURH => todo!(),
            Op::STXP => todo!(),
            Op::STXR => todo!(),
            Op::STXRB => todo!(),
            Op::STXRH => todo!(),
            Op::STZ2G => todo!(),
            Op::STZG => todo!(),
            Op::STZGM => todo!(),
            Op::SUBG => todo!(),
            Op::SUBHN => todo!(),
            Op::SUBHN2 => todo!(),
            Op::SUBHNB => todo!(),
            Op::SUBHNT => todo!(),
            Op::SUBP => todo!(),
            Op::SUBPS => todo!(),
            Op::SUBR => todo!(),
            Op::SUBS => todo!(),
            Op::SUDOT => todo!(),
            Op::SUMOPA => todo!(),
            Op::SUMOPS => todo!(),
            Op::SUNPKHI => todo!(),
            Op::SUNPKLO => todo!(),
            Op::SUQADD => todo!(),
            Op::SVC => todo!(),
            Op::SWP => todo!(),
            Op::SWPA => todo!(),
            Op::SWPAB => todo!(),
            Op::SWPAH => todo!(),
            Op::SWPAL => todo!(),
            Op::SWPALB => todo!(),
            Op::SWPALH => todo!(),
            Op::SWPB => todo!(),
            Op::SWPH => todo!(),
            Op::SWPL => todo!(),
            Op::SWPLB => todo!(),
            Op::SWPLH => todo!(),
            Op::SXTB => todo!(),
            Op::SXTH => todo!(),
            Op::SXTL => todo!(),
            Op::SXTL2 => todo!(),
            Op::SXTW => todo!(),
            Op::SYS => todo!(),
            Op::SYSL => todo!(),
            Op::TBL => todo!(),
            Op::TBNZ => todo!(),
            Op::TBX => todo!(),
            Op::TBZ => todo!(),
            Op::TCANCEL => todo!(),
            Op::TCOMMIT => todo!(),
            Op::TLBI => todo!(),
            Op::TRN1 => todo!(),
            Op::TRN2 => todo!(),
            Op::TSB => todo!(),
            Op::TST => todo!(),
            Op::TSTART => todo!(),
            Op::TTEST => todo!(),
            Op::UABA => todo!(),
            Op::UABAL => todo!(),
            Op::UABAL2 => todo!(),
            Op::UABALB => todo!(),
            Op::UABALT => todo!(),
            Op::UABD => todo!(),
            Op::UABDL => todo!(),
            Op::UABDL2 => todo!(),
            Op::UABDLB => todo!(),
            Op::UABDLT => todo!(),
            Op::UADALP => todo!(),
            Op::UADDL => todo!(),
            Op::UADDL2 => todo!(),
            Op::UADDLB => todo!(),
            Op::UADDLP => todo!(),
            Op::UADDLT => todo!(),
            Op::UADDLV => todo!(),
            Op::UADDV => todo!(),
            Op::UADDW => todo!(),
            Op::UADDW2 => todo!(),
            Op::UADDWB => todo!(),
            Op::UADDWT => todo!(),
            Op::UBFIZ => todo!(),
            Op::UBFM => todo!(),
            Op::UBFX => todo!(),
            Op::UCLAMP => todo!(),
            Op::UCVTF => todo!(),
            Op::UDF => todo!(),
            Op::UDIV => todo!(),
            Op::UDIVR => todo!(),
            Op::UDOT => todo!(),
            Op::UHADD => todo!(),
            Op::UHSUB => todo!(),
            Op::UHSUBR => todo!(),
            Op::UMADDL => todo!(),
            Op::UMAX => todo!(),
            Op::UMAXP => todo!(),
            Op::UMAXV => todo!(),
            Op::UMIN => todo!(),
            Op::UMINP => todo!(),
            Op::UMINV => todo!(),
            Op::UMLAL => todo!(),
            Op::UMLAL2 => todo!(),
            Op::UMLALB => todo!(),
            Op::UMLALT => todo!(),
            Op::UMLSL => todo!(),
            Op::UMLSL2 => todo!(),
            Op::UMLSLB => todo!(),
            Op::UMLSLT => todo!(),
            Op::UMMLA => todo!(),
            Op::UMNEGL => todo!(),
            Op::UMOPA => todo!(),
            Op::UMOPS => todo!(),
            Op::UMOV => todo!(),
            Op::UMSUBL => todo!(),
            Op::UMULH => todo!(),
            Op::UMULL => todo!(),
            Op::UMULL2 => todo!(),
            Op::UMULLB => todo!(),
            Op::UMULLT => todo!(),
            Op::UQADD => todo!(),
            Op::UQDECB => todo!(),
            Op::UQDECD => todo!(),
            Op::UQDECH => todo!(),
            Op::UQDECP => todo!(),
            Op::UQDECW => todo!(),
            Op::UQINCB => todo!(),
            Op::UQINCD => todo!(),
            Op::UQINCH => todo!(),
            Op::UQINCP => todo!(),
            Op::UQINCW => todo!(),
            Op::UQRSHL => todo!(),
            Op::UQRSHLR => todo!(),
            Op::UQRSHRN => todo!(),
            Op::UQRSHRN2 => todo!(),
            Op::UQRSHRNB => todo!(),
            Op::UQRSHRNT => todo!(),
            Op::UQSHL => todo!(),
            Op::UQSHLR => todo!(),
            Op::UQSHRN => todo!(),
            Op::UQSHRN2 => todo!(),
            Op::UQSHRNB => todo!(),
            Op::UQSHRNT => todo!(),
            Op::UQSUB => todo!(),
            Op::UQSUBR => todo!(),
            Op::UQXTN => todo!(),
            Op::UQXTN2 => todo!(),
            Op::UQXTNB => todo!(),
            Op::UQXTNT => todo!(),
            Op::URECPE => todo!(),
            Op::URHADD => todo!(),
            Op::URSHL => todo!(),
            Op::URSHLR => todo!(),
            Op::URSHR => todo!(),
            Op::URSQRTE => todo!(),
            Op::URSRA => todo!(),
            Op::USDOT => todo!(),
            Op::USHL => todo!(),
            Op::USHLL => todo!(),
            Op::USHLL2 => todo!(),
            Op::USHLLB => todo!(),
            Op::USHLLT => todo!(),
            Op::USHR => todo!(),
            Op::USMMLA => todo!(),
            Op::USMOPA => todo!(),
            Op::USMOPS => todo!(),
            Op::USQADD => todo!(),
            Op::USRA => todo!(),
            Op::USUBL => todo!(),
            Op::USUBL2 => todo!(),
            Op::USUBLB => todo!(),
            Op::USUBLT => todo!(),
            Op::USUBW => todo!(),
            Op::USUBW2 => todo!(),
            Op::USUBWB => todo!(),
            Op::USUBWT => todo!(),
            Op::UUNPKHI => todo!(),
            Op::UUNPKLO => todo!(),
            Op::UXTB => todo!(),
            Op::UXTH => todo!(),
            Op::UXTL => todo!(),
            Op::UXTL2 => todo!(),
            Op::UXTW => todo!(),
            Op::UZP1 => todo!(),
            Op::UZP2 => todo!(),
            Op::WFE => todo!(),
            Op::WFET => todo!(),
            Op::WFI => todo!(),
            Op::WFIT => todo!(),
            Op::WHILEGE => todo!(),
            Op::WHILEGT => todo!(),
            Op::WHILEHI => todo!(),
            Op::WHILEHS => todo!(),
            Op::WHILELE => todo!(),
            Op::WHILELO => todo!(),
            Op::WHILELS => todo!(),
            Op::WHILELT => todo!(),
            Op::WHILERW => todo!(),
            Op::WHILEWR => todo!(),
            Op::WRFFR => todo!(),
            Op::XAFLAG => todo!(),
            Op::XAR => todo!(),
            Op::XPACD => todo!(),
            Op::XPACI => todo!(),
            Op::XPACLRI => todo!(),
            Op::XTN => todo!(),
            Op::XTN2 => todo!(),
            Op::YIELD => todo!(),
            Op::ZERO => todo!(),
            Op::ZIP1 => todo!(),
            Op::ZIP2 => todo!(),
        }
    }
}

// fn declare_variables(
//     int: types::Type,
//     builder: &mut FunctionBuilder,
//     // params: &[String],
//     the_return: bad64::Reg,
//     stmts: &[Expr],
//     entry_block: Block,
// ) -> IndexMap<bad64::Reg, Variable> {
//     let mut variables = IndexMap::new();

//     // for (i, name) in function_params.iter().enumerate() {
//     //     // TODO: cranelift_frontend should really have an API to make it easy to set
//     //     // up param variables.
//     //     let val = builder.block_params(entry_block)[i];
//     //     let var = declare_variable(int, builder, &mut variables, name);
//     //     builder.def_var(var, val);
//     // }
//     let zero = builder.ins().iconst(int, 0);
//     let return_variable = declare_variable(int, builder, &mut variables, the_return);
//     builder.def_var(return_variable, zero);
//     for expr in stmts {
//         declare_variables_in_stmt(int, builder, &mut variables, expr);
//     }

//     variables
// }

// /// Recursively descend through the AST, translating all implicit
// /// variable declarations.
// fn declare_variables_in_stmt(
//     int: types::Type,
//     builder: &mut FunctionBuilder,
//     variables: &mut IndexMap<String, Variable>,
//     expr: &Expr,
// ) {
//     match *expr {
//         Expr::Assign(ref name, _) => {
//             declare_variable(int, builder, variables, name);
//         }
//         Expr::IfElse(ref _condition, ref then_body, ref else_body) => {
//             for stmt in then_body {
//                 declare_variables_in_stmt(int, builder, variables, stmt);
//             }
//             for stmt in else_body {
//                 declare_variables_in_stmt(int, builder, variables, stmt);
//             }
//         }
//         Expr::WhileLoop(ref _condition, ref loop_body) => {
//             for stmt in loop_body {
//                 declare_variables_in_stmt(int, builder, variables, stmt);
//             }
//         }
//         _ => (),
//     }
// }

/// Declare a single variable declaration.
fn declare_variable(
    int: types::Type,
    builder: &mut FunctionBuilder,
    variables: &mut IndexMap<bad64::Reg, Variable>,
    name: bad64::Reg,
) -> Variable {
    let var = Variable::new(variables.len());
    if !variables.contains_key(&name) {
        variables.insert(name, var);
        builder.declare_var(var, int);
    }
    var
}
