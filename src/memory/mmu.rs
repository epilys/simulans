// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! MMU - Address Translation

use std::mem::MaybeUninit;

use bilge::prelude::*;

use crate::{
    cpu_state::{
        ExceptionLevel, ExitRequest, Granule, TranslationControlRegister,
        TranslationTableBaseRegister, PSTATE,
    },
    exceptions::{AccessDescriptor, AccessType, Fault, FaultRecord},
    get_bits,
    machine::Armv8AMachine,
    memory::{Address, MemoryRegion},
    tracing::{self, TraceItem},
};

mod descriptors;
use descriptors::*;

fn align(x: u64, y: u64) -> u64 {
    y * (x / y)
}

fn is_aligned(x: u64, y: u64) -> bool {
    x == align(x, y)
}

#[repr(C)]
/// A resolved address for a translated block.
pub struct ResolvedAddress<'a> {
    /// Memory region this block resides.
    pub mem_region: &'a MemoryRegion,
    /// The offset inside this region.
    pub address_inside_region: u64,
    pub physical: Address,
}

impl Armv8AMachine {
    /// Perform a read of `SIZE` bytes
    ///
    /// `Mem[] - non-assignment (read) form`
    pub fn mem<const SIZE: usize>(
        &self,
        address: Address,
        ret: &mut [u8; SIZE],
        unprivileged: bool,
        preferred_exception_return: Address,
    ) -> Result<(), ExitRequest> {
        assert!([1, 2, 4, 8, 16, 32].contains(&SIZE));
        let aligned: bool = is_aligned(address.0, SIZE as u64);
        // if !aligned && AArch64.UnalignedAccessFaults(accdesc, address, size) then
        // constant FaultRecord fault = AlignmentFault(accdesc, address);
        // AArch64.Abort(fault);
        if aligned {
            let ResolvedAddress {
                mem_region,
                address_inside_region,
                ..
            } = self.translate_address(address, preferred_exception_return, unprivileged, true)?;
            match SIZE {
                1 => {
                    ret[0] = mem_region.read_8(address_inside_region)?;
                }
                2 => {
                    ret.copy_from_slice(&mem_region.read_16(address_inside_region)?.to_le_bytes());
                }
                4 => {
                    ret.copy_from_slice(&mem_region.read_32(address_inside_region)?.to_le_bytes());
                }
                8 => {
                    ret.copy_from_slice(&mem_region.read_64(address_inside_region)?.to_le_bytes());
                }
                16 => {
                    ret.copy_from_slice(&mem_region.read_128(address_inside_region)?.to_le_bytes());
                }
                32 => {
                    unimplemented!();
                }
                _ => unreachable!(),
            }
        } else {
            assert!(SIZE > 1);

            let mut address = address;
            for byte in ret.iter_mut().take(SIZE) {
                let ResolvedAddress {
                    mem_region,
                    address_inside_region,
                    ..
                } = self.translate_address(
                    address,
                    preferred_exception_return,
                    unprivileged,
                    true,
                )?;
                *byte = mem_region.read_8(address_inside_region)?;
                address = Address(address.0 + 1);
            }
        }
        Ok(())
    }

    /// Perform a write of `SIZE` bytes
    pub fn mem_write<const SIZE: usize>(
        &mut self,
        address: Address,
        value: &[u8; SIZE],
        unprivileged: bool,
        preferred_exception_return: Address,
    ) -> Result<(), ExitRequest> {
        assert!([1, 2, 4, 8, 16, 32].contains(&SIZE));
        let aligned: bool = is_aligned(address.0, SIZE as u64);
        // if !aligned && AArch64.UnalignedAccessFaults(accdesc, address, size) then
        // constant FaultRecord fault = AlignmentFault(accdesc, address);
        // AArch64.Abort(fault);
        if aligned {
            let ResolvedAddress {
                mem_region: _,
                address_inside_region,
                physical,
            } = self.translate_address(address, preferred_exception_return, unprivileged, true)?;
            let mem_region = self.memory.find_region_mut(physical).unwrap();
            match SIZE {
                1 => {
                    mem_region.write_8(address_inside_region, value[0])?;
                }
                2 => {
                    let value: [u8; 2] = value.as_slice().try_into().unwrap();
                    mem_region.write_16(address_inside_region, u16::from_le_bytes(value))?;
                }
                4 => {
                    let value: [u8; 4] = value.as_slice().try_into().unwrap();
                    mem_region.write_32(address_inside_region, u32::from_le_bytes(value))?;
                }
                8 => {
                    let value: [u8; 8] = value.as_slice().try_into().unwrap();
                    mem_region.write_64(address_inside_region, u64::from_le_bytes(value))?;
                }
                16 => {
                    let value: [u8; 16] = value.as_slice().try_into().unwrap();
                    mem_region.write_128(address_inside_region, u128::from_le_bytes(value))?;
                }
                32 => {
                    unimplemented!();
                }
                _ => unreachable!(),
            }
            self.invalidate
                .extend(physical.0..(physical.0 + SIZE as u64));
        } else {
            assert!(SIZE > 1);

            let mut address = address;
            for byte in value.iter().take(SIZE) {
                let ResolvedAddress {
                    mem_region: _,
                    address_inside_region,
                    physical,
                } = self.translate_address(
                    address,
                    preferred_exception_return,
                    unprivileged,
                    true,
                )?;
                let mem_region = self.memory.find_region_mut(physical).unwrap();
                mem_region.write_8(address_inside_region, *byte)?;
                address = Address(address.0 + 1);
                self.invalidate.push(physical.0);
            }
        }
        Ok(())
    }

    /// Look up memory region for given physical address.
    pub fn physical_address_lookup(
        &'_ self,
        address: Address,
        preferred_exception_return: Address,
    ) -> Result<ResolvedAddress<'_>, ExitRequest> {
        let Some(mem_region) = self.memory.find_region(address) else {
            return Err({
                let accessdesc =
                    AccessDescriptor::new(true, &self.cpu_state.PSTATE(), AccessType::TTW);
                let mut fault = FaultRecord::no_fault(accessdesc, address);
                fault.statuscode = Fault::Translation;
                ExitRequest::Abort {
                    fault,
                    preferred_exception_return,
                }
            });
        };
        let address_inside_region = address.0 - mem_region.phys_offset.0;
        Ok(ResolvedAddress {
            mem_region,
            address_inside_region,
            physical: address,
        })
    }

    /// `AArch64.TranslateAddress`
    ///
    /// Merged with `AArch64.FullTranslate`.
    pub fn translate_address(
        &'_ self,
        input_address: Address,
        preferred_exception_return: Address,
        unprivileged: bool,
        trace: bool,
    ) -> Result<ResolvedAddress<'_>, ExitRequest> {
        // [ref:TODO]: rename to S1 translation and add S2 stub
        let pstate = self.cpu_state.PSTATE();
        let sctlr = self.cpu_state.sctlr_elx();
        let privileged = if unprivileged {
            is_unpriv_access_priv(&pstate)
        } else {
            pstate.EL() != ExceptionLevel::EL0
        };

        if sctlr & 0x1 == 0 {
            // stage 1 MMU disabled
            return self.physical_address_lookup(input_address, preferred_exception_return);
        }
        let mut ttwstate = TTWState::new(self, &input_address);
        {
            let vpn = input_address.0 >> 12;
            if let Some(page) = self.tlb.get(&(ttwstate.asid, vpn)) {
                let output_address = Address(page | get_bits!(input_address.0, off = 0, len = 12));
                if trace {
                    tracing::event!(
                        target: TraceItem::AddressLookup.as_str(),
                        tracing::Level::TRACE,
                        vaddress = ?input_address,
                        resolved_paddress = ?output_address,
                        tlb_hit = true,
                    );
                }
                return self.physical_address_lookup(output_address, preferred_exception_return);
            }
        }

        let accessdesc = AccessDescriptor::new(privileged, &pstate, AccessType::TTW);

        let descriptor = self.s1_walk(
            &mut ttwstate,
            &accessdesc,
            input_address,
            preferred_exception_return,
            unprivileged,
            trace,
        )?;
        let output_address = descriptor.stage_output_address(input_address, &ttwstate);
        if trace {
            tracing::event!(
                target: TraceItem::AddressLookup.as_str(),
                tracing::Level::TRACE,
                resolved_address = ?output_address,
            );
        }
        let physical = self.physical_address_lookup(output_address, preferred_exception_return)?;
        {
            let vpn = input_address.0 >> 12;
            let page = output_address.0 >> 12;
            let page = page << 12;
            self.tlb.insert((ttwstate.asid, vpn), page);
        }
        Ok(physical)
    }

    fn s1_walk(
        &self,
        ttwstate: &mut TTWState,
        accessdesc: &AccessDescriptor,
        input_address: Address,
        preferred_exception_return: Address,
        unprivileged: bool,
        trace: bool,
    ) -> Result<Descriptor, ExitRequest> {
        let mut fault = FaultRecord::no_fault(*accessdesc, input_address);
        let pstate = self.cpu_state.PSTATE();
        let page_table_base_address: Address =
            TranslationTableBaseRegister::from(ttwstate.ttbr.0).base_address(ttwstate);

        if trace {
            tracing::event!(
                target: TraceItem::AddressLookup.as_str(),
                tracing::Level::TRACE,
                physical = false,
                address = ?input_address,
                pc = ?Address(self.pc),
                EL = ?pstate.EL(),
                ?unprivileged,
                ?ttwstate,
                ?accessdesc,
                ?page_table_base_address
            );
        }

        macro_rules! read_table_entry {
            ($base_addr:expr, $idx:expr) => {{
                let base_addr = $base_addr.0;
                let idx = u64::from($idx);
                // For the VMSAv8-64 translation system, an entry is an eight-byte, or 64-bit,
                // object
                let ResolvedAddress {
                    mem_region,
                    address_inside_region,
                    physical: _,
                } = self.physical_address_lookup(
                    Address(base_addr + idx),
                    preferred_exception_return,
                )?;
                mem_region.read_64(address_inside_region)?
            }};
        }
        match ttwstate.granule {
            Granule::_4KB => {
                // Extract translation table indices for each level OR output address bits.
                let mut base_address = page_table_base_address;

                let table_entry_0 =
                    read_table_entry!(base_address, IA4KB::idx(input_address.0, ttwstate));
                if trace {
                    tracing::event!(
                        target: TraceItem::AddressLookup.as_str(),
                        tracing::Level::TRACE,
                        ?base_address,
                        level = ttwstate.level,
                        table_entry_0 = ?tracing::BinaryHex(table_entry_0),
                    );
                }

                base_address = match table_entry_0 & 0b11 {
                    0b11 if ttwstate.level == 3 => {
                        // Page descriptor
                        let page_desc = PageDescriptor::new(table_entry_0, ttwstate);
                        return Ok(Descriptor::Page(page_desc));
                    }
                    0b11 => {
                        // Table descriptor
                        TableDescriptor::new(table_entry_0, ttwstate).entry_address
                    }
                    0b01 => {
                        // Block descriptor
                        let block_desc = BlockDescriptor::new(table_entry_0, ttwstate);
                        return Ok(Descriptor::Block(block_desc));
                    }
                    other => {
                        tracing::debug!(target: TraceItem::AddressLookup.as_str(), "invalid table entry type 0b{other:b}");
                        fault.statuscode = Fault::Translation;
                        return Err(ExitRequest::Abort {
                            fault,
                            preferred_exception_return,
                        });
                    }
                };
                ttwstate.level += 1;
                fault.level += 1;

                let table_entry_1 =
                    read_table_entry!(base_address, IA4KB::idx(input_address.0, ttwstate));
                if trace {
                    tracing::event!(
                        target: TraceItem::AddressLookup.as_str(),
                        tracing::Level::TRACE,
                        ?base_address,
                        level = ttwstate.level,
                        table_entry_1 = ?tracing::BinaryHex(table_entry_1),
                    );
                }

                base_address = match table_entry_1 & 0b11 {
                    0b11 if ttwstate.level == 3 => {
                        // Page descriptor
                        let page_desc = PageDescriptor::new(table_entry_1, ttwstate);
                        return Ok(Descriptor::Page(page_desc));
                    }
                    0b11 => {
                        // Table descriptor
                        TableDescriptor::new(table_entry_1, ttwstate).entry_address
                    }
                    0b01 => {
                        // Block descriptor
                        let block_desc = BlockDescriptor::new(table_entry_1, ttwstate);
                        return Ok(Descriptor::Block(block_desc));
                    }
                    other => {
                        tracing::debug!(target: TraceItem::AddressLookup.as_str(), "invalid table entry type 0b{other:b}");
                        fault.statuscode = Fault::Translation;
                        return Err(ExitRequest::Abort {
                            fault,
                            preferred_exception_return,
                        });
                    }
                };
                ttwstate.level += 1;
                fault.level += 1;

                let table_entry_2 =
                    read_table_entry!(base_address, IA4KB::idx(input_address.0, ttwstate));
                if trace {
                    tracing::event!(
                        target: TraceItem::AddressLookup.as_str(),
                        tracing::Level::TRACE,
                        ?base_address,
                        level = ttwstate.level,
                        table_entry_2 = ?tracing::BinaryHex(table_entry_2),
                    );
                }

                base_address = match table_entry_2 & 0b11 {
                    0b11 if ttwstate.level == 3 => {
                        // Page descriptor
                        return Ok(Descriptor::Page(PageDescriptor::new(
                            table_entry_2,
                            ttwstate,
                        )));
                    }
                    0b11 => {
                        // Table descriptor
                        TableDescriptor::new(table_entry_2, ttwstate).entry_address
                    }
                    0b01 => {
                        // Block descriptor
                        return Ok(Descriptor::Block(BlockDescriptor::new(
                            table_entry_2,
                            ttwstate,
                        )));
                    }
                    other => {
                        tracing::debug!(target: TraceItem::AddressLookup.as_str(), "invalid table entry type 0b{other:b}");
                        fault.statuscode = Fault::Translation;
                        return Err(ExitRequest::Abort {
                            fault,
                            preferred_exception_return,
                        });
                    }
                };
                ttwstate.level += 1;
                // Block descriptor
                Ok(Descriptor::Block(BlockDescriptor::new(
                    base_address.0,
                    ttwstate,
                )))
            }
            Granule::_16KB | Granule::_64KB => {
                unimplemented!()
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
/// The translation regime
pub enum Regime {
    // EL3
    EL3,
    // // EL3&0 (PL1&0 when EL3 is AArch32)
    // EL30,
    // EL2
    EL2,
    // EL2&0
    EL20,
    // EL1&0
    EL10,
}

/// Returns translation regime based on current exception level
fn translation_regime(machine: &Armv8AMachine) -> Regime {
    let pstate = machine.cpu_state.PSTATE();
    match pstate.EL() {
        ExceptionLevel::EL3 => {
            // if ELUsingAArch32(EL3) then Regime_EL30
            Regime::EL3
        }
        ExceptionLevel::EL2 => {
            // if ELIsInHost(EL2) then Regime_EL20
            Regime::EL2
        }
        ExceptionLevel::EL1 | ExceptionLevel::EL0 => Regime::EL10,
    }
}

/// Virtual address ranges
#[derive(Copy, Clone, Debug)]
pub enum VARange {
    /// `TTBR0_x`
    Lower,
    /// `TTBR1_x`
    Upper,
}

// `AArch64.GetVARange()`
impl From<&Address> for VARange {
    fn from(addr: &Address) -> Self {
        if get_bits!(addr.0, off = 55, len = 1) == 0 {
            Self::Lower
        } else {
            Self::Upper
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct TTWState {
    #[allow(dead_code)]
    va_range: VARange,
    #[allow(dead_code)]
    regime: Regime,
    asid: u16,
    level: u8,
    granule: Granule,
    ttbr: Address,
    ds: bool,
}

impl TranslationTableBaseRegister {
    fn base_address(&self, ttwstate: &TTWState) -> Address {
        let raw: u64 = (*self).into();
        Address(match ttwstate.granule {
            Granule::_4KB => get_bits!(raw, off = 12, len = 47 - 12) << 12,
            Granule::_16KB => get_bits!(raw, off = 14, len = 47 - 14) << 14,
            Granule::_64KB => get_bits!(raw, off = 16, len = 47 - 16) << 16,
        })
    }
}

const FINAL_LEVEL: u8 = 3;

// `AArch64.S1MinTxSZ`
fn s1_min_tx_sz(_regime: Regime, _d128: bool, _ds: bool, _tgx: Granule) -> u8 {
    16
}

// `AArch64.MaxTxSZ`
// Retrieve the maximum value of TxSZ indicating minimum input address size for
// both stages of translation
fn max_tx_sz(_tgx: Granule) -> u8 {
    39
}

impl TTWState {
    fn new(machine: &Armv8AMachine, input_address: &Address) -> Self {
        let regime = translation_regime(machine);
        let tcr = TranslationControlRegister::from(machine.cpu_state.tcr_elx());

        let va_range = VARange::from(input_address);

        let ttbr = Address(match (va_range, regime) {
            (_, Regime::EL3) => machine.cpu_state.mmu_registers.ttbr0_el3,
            (_, Regime::EL2) => machine.cpu_state.mmu_registers.ttbr0_el2,
            (VARange::Lower, Regime::EL20) => machine.cpu_state.mmu_registers.ttbr0_el2,
            (VARange::Upper, Regime::EL20) => machine.cpu_state.mmu_registers.ttbr1_el2,
            (VARange::Lower, Regime::EL10) => machine.cpu_state.mmu_registers.ttbr0_el1,
            (VARange::Upper, Regime::EL10) => machine.cpu_state.mmu_registers.ttbr1_el1,
        });
        let asid = if !tcr.A1() {
            let ttbr0 = match regime {
                Regime::EL3 => machine.cpu_state.mmu_registers.ttbr0_el3,
                Regime::EL2 => machine.cpu_state.mmu_registers.ttbr0_el2,
                Regime::EL20 => machine.cpu_state.mmu_registers.ttbr0_el2,
                Regime::EL10 => machine.cpu_state.mmu_registers.ttbr0_el1,
            };
            TranslationTableBaseRegister::from(ttbr0).ASID()
        } else {
            let ttbr1 = match regime {
                Regime::EL3 => unimplemented!(),
                Regime::EL2 => unimplemented!(),
                Regime::EL20 => machine.cpu_state.mmu_registers.ttbr1_el2,
                Regime::EL10 => machine.cpu_state.mmu_registers.ttbr1_el1,
            };
            TranslationTableBaseRegister::from(ttbr1).ASID()
        };

        let (granule, mut tsz, ds): (_, u8, _) = match va_range {
            VARange::Upper => (tcr.ttbr1_granule(), tcr.T1SZ().into(), tcr.DS().into()),
            VARange::Lower => (tcr.ttbr0_granule(), tcr.T0SZ().into(), tcr.DS().into()),
        };

        let s1mintxsz = s1_min_tx_sz(regime, false, ds, granule);
        let s1maxtxsz = max_tx_sz(granule);
        if tsz < s1mintxsz {
            tsz = s1mintxsz;
        } else if tsz > s1maxtxsz {
            tsz = s1maxtxsz;
        }

        // Determine initial lookup level
        // `AArch64.S1StartLevel`
        // Input Address size
        let iasize = 64 - tsz;
        let granulebits = granule.bits();
        let descsizelog2 = 3; //if d128 { 4 } else { 3 };
        let stride = granulebits - descsizelog2;
        let s1startlevel = FINAL_LEVEL - (((iasize - 1) - granulebits) / stride);
        // if walkparams.d128 == '1' then
        // s1startlevel = s1startlevel + UInt(walkparams.skl);
        Self {
            level: s1startlevel,
            va_range,
            asid,
            regime,
            ttbr,
            granule,
            ds,
        }
    }
}

#[bitsize(64)]
#[derive(Default, Copy, Clone, FromBits, DebugBits)]
struct IA4KB {
    block_offset: u12,
    level_3_idx: u9,
    level_2_idx: u9,
    level_1_idx: u9,
    level_0_idx: u9,
    res_0: u16,
}

impl IA4KB {
    // `S1SLTTEntryAddress`
    fn idx(input_address: u64, ttwstate: &TTWState) -> u64 {
        let granulebits = ttwstate.granule.bits();
        let descsizelog2 = 3; // if d128 { 4 } else { 3 };
        let stride = granulebits - descsizelog2;
        let levels = FINAL_LEVEL - ttwstate.level;
        let lsb = levels * stride + granulebits;
        let nstride = 1; // if walkparams.d128 == '1' then UInt(skl) + 1 else 1;
        let msb = (lsb + (stride * nstride)) - 1;
        // index = ZeroExtend(ia<msb:lsb>:Zeros(descsizelog2), 56);
        get_bits!(input_address, off = lsb, len = msb - lsb + 1) << descsizelog2
    }
}

/// Returns `true` if an unprivileged access is privileged, and `false`
/// otherwise.
// `AArch64.IsUnprivAccessPriv`
fn is_unpriv_access_priv(pstate: &PSTATE) -> bool {
    match pstate.EL() {
        ExceptionLevel::EL0 => false,
        // when EL1 privileged = EffectiveHCR_EL2_NVx()<1:0> == '11';
        // when EL2 privileged = !ELIsInHost(EL0);
        _ => true,
        // if IsFeatureImplemented(FEAT_UAO) && PSTATE.UAO == '1' then
        //     privileged = PSTATE.EL != EL0;
    }
}

/// `AArch64.TranslateAddress`
///
/// Merged with `AArch64.FullTranslate`.
pub extern "C" fn translate_address<'machine>(
    machine: &'machine Armv8AMachine,
    input_address: Address,
    preferred_exception_return: Address,
    raise_exception: bool,
    unprivileged: bool,
    ret: &mut MaybeUninit<ResolvedAddress<'machine>>,
) -> bool {
    match machine.translate_address(
        input_address,
        preferred_exception_return,
        unprivileged,
        raise_exception,
    ) {
        Ok(resolved) => {
            ret.write(resolved);
            true
        }
        Err(exit_request) => {
            if raise_exception {
                *machine.cpu_state.exit_request.lock().unwrap() = Some(exit_request);
            }
            false
        }
    }
}

/// `AArch64.MemZero`
pub extern "C" fn mem_zero(
    machine: &mut Armv8AMachine,
    input_address: Address,
    preferred_exception_return: Address,
) -> bool {
    const MAX_ZERO_BLOCK_SIZE: u64 = 2048;
    let size =
        4 * 2_u64.pow(get_bits!(machine.cpu_state.id_registers.dczid_el0, off = 0, len = 4) as u32);
    assert!(size <= MAX_ZERO_BLOCK_SIZE);
    let mut address = Address(align(input_address.0, size));

    for _ in 0..size {
        let ResolvedAddress {
            mem_region: _,
            address_inside_region,
            physical,
        } = match machine.translate_address(address, preferred_exception_return, false, true) {
            Ok(r) => r,
            Err(exit_request) => {
                *machine.cpu_state.exit_request.lock().unwrap() = Some(exit_request);
                return false;
            }
        };
        let mem_region = machine.memory.find_region_mut(physical).unwrap();
        if let Err(exit_request) = mem_region.write_8(address_inside_region, 0) {
            *machine.cpu_state.exit_request.lock().unwrap() = Some(exit_request);
            return false;
        }
        address = Address(address.0 + 1);
        machine.invalidate.push(physical.0);
    }
    true
}

pub extern "C" fn tlbi(machine: &Armv8AMachine) {
    machine.tlb.clear();
}

pub mod ops {
    //! Helper memory I/O functions for JIT code.

    use std::mem::MaybeUninit;

    use super::*;
    use crate::cpu_state::ExitRequest;

    macro_rules! def_op {
        (read $fn:ident: $size:ty) => {
            /// Helper memory read struct called from JIT code.
            pub extern "C" fn $fn(
                machine: &Armv8AMachine,
                address: Address,
                ret: &mut MaybeUninit<$size>,
                unprivileged: bool,
                preferred_exception_return: Address,
                exception: &mut MaybeUninit<ExitRequest>,
            ) -> bool {
                let mut v = (0 as $size).to_le_bytes();
                match machine.mem(address, &mut v, unprivileged, preferred_exception_return) {
                    Ok(()) => {
                        let value = <$size>::from_le_bytes(v);
                        ret.write(value);
                        true
                    }
                    Err(err) => {
                        exception.write(err);
                        false
                    }
                }
            }
        };
        (write $fn:ident: $size:ty) => {
            /// Helper memory write struct called from JIT code.
            pub extern "C" fn $fn(
                machine: &mut Armv8AMachine,
                address: Address,
                value: $size,
                unprivileged: bool,
                preferred_exception_return: Address,
                exception: &mut MaybeUninit<ExitRequest>,
            ) -> bool {
                let v = value.to_le_bytes();
                match machine.mem_write(address, &v, unprivileged, preferred_exception_return) {
                    Ok(()) => true,
                    Err(err) => {
                        exception.write(err);
                        false
                    }
                }
            }
        };
    }

    def_op! { write write_8: u8 }
    def_op! { write write_16: u16 }
    def_op! { write write_32: u32 }
    def_op! { write write_64: u64 }
    def_op! { write write_128: u128 }

    def_op! { read read_8: u8 }
    def_op! { read read_16: u16 }
    def_op! { read read_32: u32 }
    def_op! { read read_64: u64 }
    def_op! { read read_128: u128 }
}
