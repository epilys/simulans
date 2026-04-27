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
        if matches!(size, Width::_128) {
            assert_eq!(e, 0);
            return simd_value;
        }
        let mut value = self.builder.ins().ushr_imm(simd_value, e * i64::from(size));
        if size < Width::_64 {
            value = self
                .builder
                .ins()
                .band_imm(value, bit_mask!(off = 0, len = size as u32));
        }
        self.builder.ins().ireduce(size.into(), value)
    }

    /// `J1.3.3.29 Elem: Elem[] - setter`
    pub fn set_elem(&mut self, simd_value: Value, e: i64, size: Width, value: Value) -> Value {
        let offset = e * i64::from(size);
        if offset >= 64 || size >= Width::_64 {
            let value = if size == Width::_64 {
                value
            } else {
                self.builder.ins().uextend(I64, value)
            };
            let (lo, hi) = self.builder.ins().isplit(simd_value);
            let (lo, hi) = if offset >= 64 {
                let offset = offset - 64;
                // Clear previous element value.
                let hi = if matches!(size, Width::_64) {
                    assert_eq!(offset, 0);
                    self.builder.ins().iconst(I64, 0)
                } else {
                    self.builder
                        .ins()
                        .band_imm(hi, !bit_mask!(off = offset, len = size as i64))
                };
                let value = self.builder.ins().ishl_imm(value, offset);
                (lo, self.builder.ins().bor(hi, value))
            } else {
                // Clear previous element value.
                let lo = if matches!(size, Width::_64) {
                    assert_eq!(offset, 0);
                    self.builder.ins().iconst(I64, 0)
                } else {
                    self.builder
                        .ins()
                        .band_imm(lo, !bit_mask!(off = offset, len = size as i64))
                };
                let value = self.builder.ins().ishl_imm(value, offset);
                (self.builder.ins().bor(lo, value), hi)
            };

            let simd_value = self.builder.ins().iconcat(lo, hi);
            self.builder
                .ins()
                .bitcast(I128, super::MEMFLAG_LITTLE_ENDIAN, simd_value)
        } else {
            let value = self.builder.ins().uextend(I128, value);
            // Clear previous element value.
            let simd_value = self
                .builder
                .ins()
                .band_imm(simd_value, !bit_mask!(off = offset, len = size as i64));
            let value = self.builder.ins().ishl_imm(value, offset);
            self.builder.ins().bor(simd_value, value)
        }
    }
}
