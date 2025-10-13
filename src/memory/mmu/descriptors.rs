// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use super::{align, Granule, TTWState, FINAL_LEVEL};
use crate::{get_bits, memory::Address};

fn align_bits(x: u64, y: u64, n: u32) -> u64 {
    get_bits!(align(x, y), off = 0, len = n - 1)
}

fn translation_size(d128: bool, tgx: Granule, level: u8) -> u64 {
    let granulebits = tgx.bits();
    let descsizelog2 = if d128 { 4 } else { 3 };
    let blockbits = u64::from(FINAL_LEVEL - level) * u64::from(granulebits - descsizelog2);
    u64::from(granulebits) + blockbits
}

#[derive(Debug)]
pub enum Descriptor {
    Block(BlockDescriptor),
    Page(PageDescriptor),
}

impl Descriptor {
    pub fn stage_output_address(self, input_address: Address, ttwstate: &TTWState) -> Address {
        match self {
            Self::Block(d) => d.stage_output_address(input_address, ttwstate),
            Self::Page(d) => d.stage_output_address(input_address, ttwstate),
        }
    }
}

#[derive(Debug)]
pub struct BlockDescriptor {
    pub output_address: Address,
    pub contiguous: bool,
}

impl BlockDescriptor {
    pub fn new(descriptor: u64, ttwstate: &TTWState) -> Self {
        assert_eq!(descriptor & 0b11, 1);
        let contiguous = if matches!(ttwstate.granule, Granule::_4KB) {
            if ttwstate.level == 0 {
                false
            } else {
                get_bits!(descriptor, off = 52, len = 1) == 1
            }
        } else {
            unimplemented!()
        };
        match (ttwstate.granule, ttwstate.ds) {
            (Granule::_4KB | Granule::_16KB, true) => {
                // 52-bit OA
                let n = match ttwstate.level {
                    0 => 39,
                    1 => 30,
                    2 => 21,
                    _ => unreachable!(),
                };
                let output_address = Address(get_bits!(descriptor, off = n, len = 49 - n) << n);
                Self {
                    output_address,
                    contiguous,
                }
            }
            (Granule::_64KB, true) => unimplemented!(),
            (_, false) => {
                // 48-bit OA
                let n = match ttwstate.granule {
                    Granule::_4KB if ttwstate.level == 0 => unreachable!(),
                    Granule::_4KB if ttwstate.level == 1 => 30,
                    Granule::_4KB if ttwstate.level == 2 => 21,
                    Granule::_16KB if ttwstate.level == 2 => 25,
                    Granule::_64KB if ttwstate.level == 2 => 29,
                    other => unreachable!("{other:?} level {:?}", ttwstate.level),
                };
                let output_address = Address(get_bits!(descriptor, off = n, len = 47 - n) << n);
                Self {
                    output_address,
                    contiguous,
                }
            }
        }
    }

    // `StageOA()`
    pub fn stage_output_address(self, input_address: Address, ttwstate: &TTWState) -> Address {
        let tsize = translation_size(false, ttwstate.granule, ttwstate.level);
        let csize = if self.contiguous { 4 } else { 0 }; //(if walkstate.contiguous == '1' then ContiguousSize(d128, tgx,
                                                         //(if walkstate.level) else 0);
        let ia_msb = tsize + csize;
        // oa.paspace = walkstate.baseaddress.paspace;
        // oa.address = walkstate.baseaddress.address<55:ia_msb>:ia<ia_msb-1:0>;
        Address(
            get_bits!(self.output_address.0, off = ia_msb, len = 55 - ia_msb) << ia_msb
                | get_bits!(input_address.0, off = 0, len = ia_msb),
        )
    }
}

#[derive(Debug)]
pub struct TableDescriptor {
    pub entry_address: Address,
}

impl TableDescriptor {
    pub fn new(descriptor: u64, ttwstate: &TTWState) -> Self {
        assert_eq!(descriptor & 0b11, 0b11);
        // AArch64.NextTableBase()
        let mut tablebase = 0;
        let granulebits = ttwstate.granule.bits();
        // if d128 == '1' then
        //     constant integer descsizelog2 = 4;
        //     let stride = granulebits - descsizelog2;
        //     let tablesize = stride*(1 + UInt(skl)) + descsizelog2;
        // else
        let tablesize = granulebits;
        match ttwstate.granule {
            Granule::_4KB => {
                tablebase |= get_bits!(descriptor, off = 12, len = 47 - 12) << 12;
            }
            Granule::_16KB => {
                tablebase |= get_bits!(descriptor, off = 14, len = 47 - 14) << 14;
            }
            Granule::_64KB => {
                tablebase |= get_bits!(descriptor, off = 16, len = 47 - 16) << 16;
            }
        }
        tablebase = align_bits(tablebase, 2_u32.pow(u32::from(tablesize)).into(), 56);
        // if d128 == '1' then
        //     tablebase<55:48> = descriptor<55:48>;
        // elsif tgx == TGx_64KB && (AArch64.PAMax() >= 52 ||
        //     boolean IMPLEMENTATION_DEFINED "descriptor[15:12] for 64KB granule are
        // OA[51:48]") then     tablebase<51:48> = descriptor<15:12>;
        // elsif ds == '1' then
        //     tablebase<51:48> = descriptor<9:8>:descriptor<49:48>;

        Self {
            entry_address: Address(tablebase),
        }
    }
}

#[derive(Debug)]
pub struct PageDescriptor {
    pub page_address: Address,
    pub contiguous: bool,
}

impl PageDescriptor {
    pub fn new(descriptor: u64, ttwstate: &TTWState) -> Self {
        assert_eq!(descriptor & 0b11, 0b11);
        let page_address = match ttwstate.granule {
            Granule::_4KB => get_bits!(descriptor, off = 12, len = 47 - 12) << 12,
            Granule::_16KB => get_bits!(descriptor, off = 14, len = 47 - 14) << 14,
            Granule::_64KB => get_bits!(descriptor, off = 16, len = 47 - 16) << 16,
        };
        let contiguous = if matches!(ttwstate.granule, Granule::_4KB) {
            if ttwstate.level == 0 {
                false
            } else {
                get_bits!(descriptor, off = 52, len = 1) == 1
            }
        } else {
            unimplemented!()
        };

        Self {
            page_address: Address(page_address),
            contiguous,
        }
    }

    pub fn stage_output_address(self, input_address: Address, ttwstate: &TTWState) -> Address {
        let tsize = translation_size(false, ttwstate.granule, ttwstate.level);
        let csize = if self.contiguous {
            //(if walkstate.contiguous == '1' then ContiguousSize(d128, tgx, (walkstate.level) else 0);
            4
        } else {
            0
        };
        let ia_msb = tsize + csize;
        // oa.paspace = walkstate.baseaddress.paspace;
        // oa.address = walkstate.baseaddress.address<55:ia_msb>:ia<ia_msb-1:0>;
        Address(
            get_bits!(self.page_address.0, off = ia_msb, len = 55 - ia_msb) << ia_msb
                | get_bits!(input_address.0, off = 0, len = ia_msb),
        )
    }
}
