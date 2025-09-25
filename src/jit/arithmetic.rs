// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Scalar arithmetic and condition flag operations

use cranelift::{
    codegen::ir::types::{I64, I8},
    prelude::*,
};

use crate::{jit::BlockTranslator, memory::Width};

const fn crc32_table<const POLYNOMIAL: u32>() -> [u32; 256] {
    let poly: u32 = POLYNOMIAL.reverse_bits();

    let mut ret = [0_u32; 256];
    let mut i = 0;
    while i < 256 {
        // remainder from polynomial division
        let mut rem = i as u32;
        let mut j = 0;
        while j < 8 {
            if rem & 1 > 0 {
                rem >>= 1;
                rem ^= poly;
            } else {
                rem >>= 1;
            }
            j += 1;
        }
        ret[i] = rem;
        i += 1;
    }
    ret
}

pub const CRC32_TABLE: [u32; 256] = crc32_table::<0x04c11db7_u32>();
pub const CRC32C_TABLE: [u32; 256] = crc32_table::<0x1edc6f41_u32>();

impl BlockTranslator<'_> {
    /// Update CPU state of NZCV flags.
    pub fn update_nzcv(&mut self, [n, z, c, v]: [Value; 4]) {
        let n = self.builder.ins().rotl_imm(n, 31);
        let z = self.builder.ins().rotl_imm(z, 30);
        let c = self.builder.ins().rotl_imm(c, 29);
        let v = self.builder.ins().rotl_imm(v, 28);
        let value = self.builder.ins().bor(n, z);
        let value = self.builder.ins().bor(value, c);
        let value = self.builder.ins().bor(value, v);
        self.write_sysreg(&bad64::SysReg::NZCV, value);
    }

    /// Perform `AddWithCarry` operation.
    ///
    /// Integer addition with carry input, returning result and NZCV flags
    pub fn add_with_carry(
        &mut self,
        x: Value,
        y: Value,
        _orig_y: Value,
        carry_in: Value,
        width: Width,
    ) -> (Value, [Value; 4]) {
        let carry_in = self.builder.ins().uextend(width.into(), carry_in);
        let (signed_sum, mut overflow) = self.builder.ins().sadd_overflow(x, y);
        {
            let (_, carry_overflow) = self.builder.ins().sadd_overflow(signed_sum, carry_in);
            overflow = self.builder.ins().bor(overflow, carry_overflow);
        }
        let (result, overflow_2) = self.builder.ins().uadd_overflow(x, y);
        let (result, mut carry_out) = self.builder.ins().uadd_overflow(result, carry_in);
        carry_out = self.builder.ins().bor(overflow_2, carry_out);
        let n = self
            .builder
            .ins()
            .icmp_imm(IntCC::SignedLessThan, result, 0);
        let z = self.builder.ins().icmp_imm(IntCC::Equal, result, 0);
        let c = self.builder.ins().icmp_imm(IntCC::NotEqual, carry_out, 0);
        let v = self.builder.ins().icmp_imm(IntCC::NotEqual, overflow, 0);
        let n = self.builder.ins().uextend(I64, n);
        let z = self.builder.ins().uextend(I64, z);
        let c = self.builder.ins().uextend(I64, c);
        let v = self.builder.ins().uextend(I64, v);
        (result, [n, z, c, v])
    }

    /// Return true iff `condition` currently holds
    ///
    /// Based on pseudocode for
    /// [`shared/functions/system/ConditionHolds`](https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/shared-functions-system?lang=en#impl-shared.ConditionHolds.1).
    pub fn condition_holds(&mut self, condition: bad64::Condition) -> Value {
        use bad64::Condition;

        let var = self.read_sysreg(&bad64::SysReg::NZCV);

        macro_rules! cmp_pstate {
            (PSTATE.N) => {{
                let n = self.builder.ins().band_imm(var, (1 << 31));
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::UnsignedGreaterThan, n, 0)
            }};
            (PSTATE.Z) => {{
                let z = self.builder.ins().band_imm(var, (1 << 30));
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::UnsignedGreaterThan, z, 0)
            }};
            (PSTATE.C) => {{
                let c = self.builder.ins().band_imm(var, (1 << 29));
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::UnsignedGreaterThan, c, 0)
            }};
            (PSTATE.V) => {{
                let v = self.builder.ins().band_imm(var, (1 << 28));
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::UnsignedGreaterThan, v, 0)
            }};
            (PSTATE.$field:ident == $imm:literal) => {{
                #[allow(non_snake_case)]
                let $field = cmp_pstate!(PSTATE.$field);
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::Equal, $field, $imm)
            }};
            (PSTATE.$field1:ident == PSTATE.$field2:ident) => {{
                #[allow(non_snake_case)]
                let $field1 = cmp_pstate!(PSTATE.$field1);
                #[allow(non_snake_case)]
                let $field2 = cmp_pstate!(PSTATE.$field2);
                self.builder
                    .ins()
                    .icmp(cranelift::prelude::IntCC::Equal, $field1, $field2)
            }};
            (( $($t1:tt)* ) && ( $($t2:tt)* )) => {{
                let result1 = cmp_pstate!($($t1)*);
                let result2 = cmp_pstate!($($t2)*);
                self.builder
                    .ins()
                    .band(result1, result2)
            }};
            (!(( $($t1:tt)* ) && ( $($t2:tt)* ))) => {{
                let result = cmp_pstate!(($($t1)*) && ($($t2)*));
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::Equal, result, 0)
            }};
        }

        // | Condition | Meaning               | A, B    | NZCV
        // |-----------|-----------------------|---------|--------------------
        // | EQ        | Equal                 | A == B  | Z == 1
        // | NE        | Not Equal             | A != B  | Z == 0
        // | CS        | Carry set             | A >= B  | C == 1
        // | CC        | Carry clear           | A < B   | C == 0
        // | HI        | Higher                | A > B   | C == 1 && Z == 0
        // | LS        | Lower or same         | A <= B  | !(C == 1 && Z == 0)
        // | GE        | Greater than or equal | A >= B  | N == V
        // | LT        | Less than             | A < B   | N != V
        // | GT        | Greater than          | A > B   | Z == 0 && N == V
        // | LE        | Less than or equal    | A <= B  | !(Z == 0 && N == V)
        // | MI        | Minus, negative       | A < B   | N == 1
        // | PL        | Plus or zero          | A >= B  | N == 0
        // | VS        | Overflow set          | -       | V == 1
        // | VC        | Overflow clear        | -       | V == 0
        // | AL, NV    | Always                | true    | -

        let result = match condition {
            Condition::EQ => {
                cmp_pstate!(PSTATE.Z == 1)
            }
            Condition::NE => {
                cmp_pstate!(PSTATE.Z == 0)
            }
            Condition::CS => {
                cmp_pstate!(PSTATE.C == 1)
            }
            Condition::CC => {
                cmp_pstate!(PSTATE.C == 0)
            }
            Condition::MI => {
                cmp_pstate!(PSTATE.N == 1)
            }
            Condition::PL => {
                cmp_pstate!(PSTATE.N == 0)
            }
            Condition::VS => {
                cmp_pstate!(PSTATE.V == 1)
            }
            Condition::VC => {
                cmp_pstate!(PSTATE.V == 0)
            }
            Condition::HI => {
                cmp_pstate!((PSTATE.C == 1) && (PSTATE.Z == 0))
            }
            Condition::LS => {
                cmp_pstate!(!((PSTATE.C == 1) && (PSTATE.Z == 0)))
            }
            Condition::GE => {
                cmp_pstate!(PSTATE.N == PSTATE.V)
            }
            Condition::LT => {
                let result = cmp_pstate!(PSTATE.N == PSTATE.V);
                self.builder
                    .ins()
                    .icmp_imm(cranelift::prelude::IntCC::Equal, result, 0)
            }
            Condition::GT => {
                cmp_pstate!((PSTATE.N == PSTATE.V) && (PSTATE.Z == 0))
            }
            Condition::LE => {
                cmp_pstate!(!((PSTATE.N == PSTATE.V) && (PSTATE.Z == 0)))
            }
            // Always true.
            Condition::AL | Condition::NV => self.builder.ins().iconst(I8, 1),
        };

        result
    }
}
