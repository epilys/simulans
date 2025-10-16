// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! SIMD instruction emulation for stuff Cranelift doesn't support.

use bad64::ArrSpec;
use codegen::ir::types::{I128, I64};
use cranelift::prelude::*;

use crate::{bit_mask, jit::BlockTranslator, memory::Width};

impl From<ArrSpec> for Width {
    fn from(arrspec: ArrSpec) -> Self {
        match arrspec {
            ArrSpec::OneHalf(_)
            | ArrSpec::FourHalves(_)
            | ArrSpec::TwoHalves(_)
            | ArrSpec::EightHalves(_) => Self::_16,
            ArrSpec::OneByte(_)
            | ArrSpec::FourBytes(_)
            | ArrSpec::EightBytes(_)
            | ArrSpec::SixteenBytes(_) => Self::_8,
            ArrSpec::OneSingle(_) | ArrSpec::TwoSingles(_) | ArrSpec::FourSingles(_) => Self::_32,
            ArrSpec::OneDouble(_) | ArrSpec::TwoDoubles(_) => Self::_64,
            ArrSpec::Full(_) => Self::_128,
        }
    }
}

impl BlockTranslator<'_> {
    // [ref:cranelift_ice]: cranelift doesn't support 128-bit iconst
    pub fn simd_iconst(&mut self, width: Width, imm: i64) -> Value {
        if width < Width::_128 {
            return self.builder.ins().iconst(width.into(), imm);
        }
        let value = self.builder.ins().iconst(I64, imm);
        self.builder.ins().uextend(I128, value)
    }

    /// `J1.3.3.29 Elem: Elem[] - getter`
    pub fn get_elem(&mut self, simd_value: Value, e: i64, size: Width) -> Value {
        let val = self.builder.ins().ushr_imm(simd_value, e * i64::from(size));
        let value = self.builder.ins().band_imm(val, 2_i64.pow(size as u32 - 1));
        self.builder.ins().ireduce(size.into(), value)
    }

    /// `J1.3.3.29 Elem: Elem[] - setter`
    pub fn set_elem(&mut self, simd_value: Value, e: i64, size: Width, value: Value) -> Value {
        let value = self.builder.ins().uextend(I128, value);
        let offset = e * i64::from(size);
        // Clear previous element value.
        let simd_value = self
            .builder
            .ins()
            .band_imm(simd_value, !bit_mask!(off = offset, len = size as i64));
        let value = self.builder.ins().ishl_imm(value, offset);
        self.builder.ins().bor(simd_value, value)
    }
}
