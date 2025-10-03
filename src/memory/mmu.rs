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

fn align(x: u64, y: u64) -> u64 {
    y * (x / y)
}

fn align_bits(x: u64, y: u64, n: u32) -> u64 {
    get_bits!(align(x, y), off = 0, len = n - 1)
}

#[repr(C)]
/// A resolved address for a translated block.
pub struct ResolvedAddress<'a> {
    /// Memory region this block resides.
    pub mem_region: Option<&'a MemoryRegion>,
    /// The offset inside this region.
    pub address_inside_region: u64,
}

/// Helper function to look up memory region for given physical address.
pub extern "C" fn physical_address_lookup<'machine>(
    machine: &'machine Armv8AMachine,
    address: Address,
    preferred_exception_return: Address,
    raise_exception: bool,
    ret: &mut MaybeUninit<ResolvedAddress<'machine>>,
) -> bool {
    if raise_exception {
        tracing::event!(
            target: TraceItem::AddressLookup.as_str(),
            tracing::Level::TRACE,
            physical = true,
            address = ?address,
            pc = ?Address(machine.pc),
        );
    }
    let Some(mem_region) = machine.memory.find_region(address) else {
        if raise_exception {
            let accessdesc =
                AccessDescriptor::new(true, &machine.cpu_state.PSTATE(), AccessType::TTW);
            let mut fault = FaultRecord::no_fault(accessdesc, address);
            fault.statuscode = Fault::Translation;
            *machine.cpu_state.exit_request.lock().unwrap() = Some(ExitRequest::Abort {
                fault,
                preferred_exception_return,
            });
            tracing::error!(
                "Could not look up address {} in physical memory map. pc was: 0x{:x}",
                address,
                machine.pc
            );
        }
        return false;
    };
    let address_inside_region = address.0 - mem_region.phys_offset.0;
    ret.write(ResolvedAddress {
        mem_region: Some(mem_region),
        address_inside_region,
    });
    true
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
struct IAParameters {
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
    fn base_address(&self, params: &IAParameters) -> Address {
        let raw: u64 = (*self).into();
        Address(match params.granule {
            Granule::_4KB => get_bits!(raw, off = 12, len = 47 - 12) << 12,
            Granule::_16KB => get_bits!(raw, off = 14, len = 47 - 14) << 14,
            Granule::_64KB => get_bits!(raw, off = 16, len = 47 - 16) << 16,
        })
    }
}

const FINAL_LEVEL: u8 = 3;

fn translation_size(d128: bool, tgx: Granule, level: u8) -> u64 {
    let granulebits = tgx.bits();
    let descsizelog2 = if d128 { 4 } else { 3 };
    let blockbits = u64::from(FINAL_LEVEL - level) * u64::from(granulebits - descsizelog2);
    u64::from(granulebits) + blockbits
}

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

impl IAParameters {
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
    fn idx(input_address: u64, params: &IAParameters) -> u64 {
        let granulebits = params.granule.bits();
        let descsizelog2 = 3; // if d128 { 4 } else { 3 };
        let stride = granulebits - descsizelog2;
        let levels = FINAL_LEVEL - params.level;
        let lsb = levels * stride + granulebits;
        let nstride = 1; // if walkparams.d128 == '1' then UInt(skl) + 1 else 1;
        let msb = (lsb + (stride * nstride)) - 1;
        // index = ZeroExtend(ia<msb:lsb>:Zeros(descsizelog2), 56);
        get_bits!(input_address, off = lsb, len = msb - lsb + 1) << descsizelog2
    }
}

#[derive(Debug)]
struct BlockDescriptor {
    output_address: Address,
}

impl BlockDescriptor {
    fn new(value: u64, params: &IAParameters) -> Self {
        assert_eq!(value & 0b11, 1);
        match (params.granule, params.ds) {
            (Granule::_4KB | Granule::_16KB, true) => {
                // 52-bit OA
                let n = match params.level {
                    0 => 39,
                    1 => 30,
                    2 => 21,
                    _ => unreachable!(),
                };
                let output_address = Address(get_bits!(value, off = n, len = 49 - n) << n);
                Self { output_address }
            }
            (Granule::_64KB, true) => unimplemented!(),
            (_, false) => {
                // 48-bit OA
                let n = match params.granule {
                    Granule::_4KB if params.level == 0 => unreachable!(),
                    Granule::_4KB if params.level == 1 => 30,
                    Granule::_4KB if params.level == 2 => 21,
                    Granule::_16KB if params.level == 2 => 25,
                    Granule::_64KB if params.level == 2 => 29,
                    other => unreachable!("{other:?} level {:?}", params.level),
                };
                let output_address = Address(get_bits!(value, off = n, len = 47 - n) << n);
                Self { output_address }
            }
        }
    }

    // `StageOA()`
    fn stage_output_address(self, input_address: Address, params: &IAParameters) -> Address {
        let tsize = translation_size(false, params.granule, params.level);
        let csize = 0; //(if walkstate.contiguous == '1' then ContiguousSize(d128, tgx,
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
struct TableDescriptor {
    entry_address: Address,
}

impl TableDescriptor {
    fn new(descriptor: u64, params: &IAParameters) -> Self {
        assert_eq!(descriptor & 0b11, 0b11);
        // AArch64.NextTableBase()
        let mut tablebase = 0;
        let granulebits = params.granule.bits();
        // if d128 == '1' then
        //     constant integer descsizelog2 = 4;
        //     let stride = granulebits - descsizelog2;
        //     let tablesize = stride*(1 + UInt(skl)) + descsizelog2;
        // else
        let tablesize = granulebits;
        match params.granule {
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
struct PageDescriptor {
    page_address: Address,
}

impl PageDescriptor {
    fn new(descriptor: u64, params: &IAParameters) -> Self {
        assert_eq!(descriptor & 0b11, 0b11);
        let page_address = match params.granule {
            Granule::_4KB => get_bits!(descriptor, off = 12, len = 47 - 12) << 12,
            Granule::_16KB => get_bits!(descriptor, off = 14, len = 47 - 14) << 14,
            Granule::_64KB => get_bits!(descriptor, off = 16, len = 47 - 16) << 16,
        };

        Self {
            page_address: Address(page_address),
        }
    }

    fn stage_output_address(self, input_address: Address, params: &IAParameters) -> Address {
        let tsize = translation_size(false, params.granule, params.level);
        let csize = 0; //(if walkstate.contiguous == '1' then ContiguousSize(d128, tgx,
                       //(if walkstate.level) else 0);
        let ia_msb = tsize + csize;
        // oa.paspace = walkstate.baseaddress.paspace;
        // oa.address = walkstate.baseaddress.address<55:ia_msb>:ia<ia_msb-1:0>;
        Address(self.page_address.0 | get_bits!(input_address.0, off = 0, len = ia_msb))
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
    // [ref:TODO]: rename to S1 translation and add S2 stub
    let pstate = machine.cpu_state.PSTATE();
    let sctlr = machine.cpu_state.sctlr_elx();
    let privileged = if unprivileged {
        is_unpriv_access_priv(&pstate)
    } else {
        pstate.EL() != ExceptionLevel::EL0
    };

    if sctlr & 0x1 == 0 {
        // stage 1 MMU disabled
        return physical_address_lookup(
            machine,
            input_address,
            preferred_exception_return,
            raise_exception,
            ret,
        );
    }
    let mut params = IAParameters::new(machine, &input_address);
    {
        let vpn = input_address.0 >> 12;
        if let Some(page) = machine.tlb.get(&(params.asid, vpn)) {
            let output_address = Address(page | get_bits!(input_address.0, off = 0, len = 12));
            return physical_address_lookup(
                machine,
                output_address,
                preferred_exception_return,
                raise_exception,
                ret,
            );
        }
    }

    let accessdesc = AccessDescriptor::new(privileged, &pstate, AccessType::TTW);
    let page_table_base_address: Address =
        TranslationTableBaseRegister::from(params.ttbr.0).base_address(&params);

    if raise_exception {
        tracing::event!(
            target: TraceItem::AddressLookup.as_str(),
            tracing::Level::TRACE,
            physical = false,
            address = ?input_address,
            pc = ?Address(machine.pc),
            EL = ?pstate.EL(),
            ?unprivileged,
            ?params,
            ?accessdesc,
            ?page_table_base_address
        );
    }
    let mut fault = FaultRecord::no_fault(accessdesc, input_address);

    macro_rules! read_table_entry {
        ($base_addr:expr, $idx:expr) => {{
            let base_addr = $base_addr.0;
            let idx = u64::from($idx);
            // For the VMSAv8-64 translation system, an entry is an eight-byte, or 64-bit,
            // object
            let mut resolved_address = MaybeUninit::uninit();
            if !physical_address_lookup(
                machine,
                Address(base_addr + idx),
                preferred_exception_return,
                raise_exception,
                &mut resolved_address
            ) {
                return false;
            }
            let ResolvedAddress {
                mem_region,
                address_inside_region,
            } =
            // SAFETY: we checked the return value
            unsafe { resolved_address.assume_init() };
            let mut resolved_value = MaybeUninit::uninit();
            let mut exception = MaybeUninit::uninit();
            if !crate::memory::region::ops::memory_region_read_64(
                mem_region.unwrap(),
                address_inside_region,
                &mut resolved_value,
                &mut exception,
            ) {
                // SAFETY: read returned false, so this is initialized
                let exception = unsafe { exception.assume_init() };
                if raise_exception {
                    *machine.cpu_state.exit_request.lock().unwrap() =
                        Some(exception);
                }
                return false;
            }
            // SAFETY: read returned true, so this is initialized
            unsafe { resolved_value.assume_init() }
        }};
    }
    match params.granule {
        Granule::_4KB => {
            // Extract translation table indices for each level OR output address bits.
            let mut base_address = page_table_base_address;

            let table_entry_0 =
                read_table_entry!(base_address, IA4KB::idx(input_address.0, &params));
            if raise_exception {
                tracing::event!(
                    target: TraceItem::AddressLookup.as_str(),
                    tracing::Level::TRACE,
                    ?base_address,
                    level = params.level,
                    table_entry_0 = ?tracing::BinaryHex(table_entry_0),
                );
            }

            base_address = match table_entry_0 & 0b11 {
                0b11 if params.level == 3 => {
                    // Page descriptor
                    let page_desc = PageDescriptor::new(table_entry_0, &params);
                    let output_address = page_desc.stage_output_address(input_address, &params);
                    if raise_exception {
                        tracing::event!(
                            target: TraceItem::AddressLookup.as_str(),
                            tracing::Level::TRACE,
                            resolved_address = ?output_address,
                        );
                    }
                    {
                        let vpn = input_address.0 >> 12;
                        let page = output_address.0 >> 12;
                        let page = page << 12;
                        machine.tlb.insert((params.asid, vpn), page);
                    }
                    return physical_address_lookup(
                        machine,
                        output_address,
                        preferred_exception_return,
                        raise_exception,
                        ret,
                    );
                }
                0b11 => {
                    // Table descriptor
                    TableDescriptor::new(table_entry_0, &params).entry_address
                }
                0b01 => {
                    // Block descriptor
                    let block_desc = BlockDescriptor::new(table_entry_0, &params);
                    let output_address = block_desc.stage_output_address(input_address, &params);
                    if raise_exception {
                        tracing::event!(
                            target: TraceItem::AddressLookup.as_str(),
                            tracing::Level::TRACE,
                            resolved_address = ?output_address
                        )
                    };
                    {
                        let vpn = input_address.0 >> 12;
                        let page = output_address.0 >> 12;
                        let page = page << 12;
                        machine.tlb.insert((params.asid, vpn), page);
                    }
                    return physical_address_lookup(
                        machine,
                        output_address,
                        preferred_exception_return,
                        raise_exception,
                        ret,
                    );
                }
                other => {
                    tracing::debug!(target: TraceItem::AddressLookup.as_str(), "invalid table entry type 0b{other:b}");
                    if raise_exception {
                        fault.statuscode = Fault::Translation;
                        *machine.cpu_state.exit_request.lock().unwrap() =
                            Some(ExitRequest::Abort {
                                fault,
                                preferred_exception_return,
                            });
                    }
                    return false;
                }
            };
            params.level += 1;
            fault.level += 1;

            let table_entry_1 =
                read_table_entry!(base_address, IA4KB::idx(input_address.0, &params));
            if raise_exception {
                tracing::event!(
                    target: TraceItem::AddressLookup.as_str(),
                    tracing::Level::TRACE,
                    ?base_address,
                    level = params.level,
                    table_entry_1 = ?tracing::BinaryHex(table_entry_1),
                );
            }

            base_address = match table_entry_1 & 0b11 {
                0b11 if params.level == 3 => {
                    // Page descriptor
                    let page_desc = PageDescriptor::new(table_entry_1, &params);
                    let output_address = page_desc.stage_output_address(input_address, &params);
                    if raise_exception {
                        tracing::event!(
                            target: TraceItem::AddressLookup.as_str(),
                            tracing::Level::TRACE,
                            resolved_address = ?output_address,
                        );
                    }
                    {
                        let vpn = input_address.0 >> 12;
                        let page = output_address.0 >> 12;
                        let page = page << 12;
                        machine.tlb.insert((params.asid, vpn), page);
                    }
                    return physical_address_lookup(
                        machine,
                        output_address,
                        preferred_exception_return,
                        raise_exception,
                        ret,
                    );
                }
                0b11 => {
                    // Table descriptor
                    TableDescriptor::new(table_entry_1, &params).entry_address
                }
                0b01 => {
                    // Block descriptor
                    let block_desc = BlockDescriptor::new(table_entry_1, &params);
                    let output_address = block_desc.stage_output_address(input_address, &params);
                    if raise_exception {
                        tracing::event!(
                            target: TraceItem::AddressLookup.as_str(),
                            tracing::Level::TRACE,
                            resolved_address = ?output_address,
                        );
                    }
                    {
                        let vpn = input_address.0 >> 12;
                        let page = output_address.0 >> 12;
                        let page = page << 12;
                        machine.tlb.insert((params.asid, vpn), page);
                    }
                    return physical_address_lookup(
                        machine,
                        output_address,
                        preferred_exception_return,
                        raise_exception,
                        ret,
                    );
                }
                other => {
                    tracing::debug!(target: TraceItem::AddressLookup.as_str(), "invalid table entry type 0b{other:b}");
                    if raise_exception {
                        fault.statuscode = Fault::Translation;
                        *machine.cpu_state.exit_request.lock().unwrap() =
                            Some(ExitRequest::Abort {
                                fault,
                                preferred_exception_return,
                            });
                    }
                    return false;
                }
            };
            params.level += 1;
            fault.level += 1;

            let table_entry_2 =
                read_table_entry!(base_address, IA4KB::idx(input_address.0, &params));
            if raise_exception {
                tracing::event!(
                    target: TraceItem::AddressLookup.as_str(),
                    tracing::Level::TRACE,
                    ?base_address,
                    level = params.level,
                    table_entry_2 = ?tracing::BinaryHex(table_entry_2),
                );
            }

            base_address = match table_entry_2 & 0b11 {
                0b11 if params.level == 3 => {
                    // Page descriptor
                    let page_desc = PageDescriptor::new(table_entry_2, &params);
                    let output_address = page_desc.stage_output_address(input_address, &params);
                    if raise_exception {
                        tracing::event!(
                            target: TraceItem::AddressLookup.as_str(),
                            tracing::Level::TRACE,
                            resolved_address = ?output_address,
                        );
                    }
                    {
                        let vpn = input_address.0 >> 12;
                        let page = output_address.0 >> 12;
                        let page = page << 12;
                        machine.tlb.insert((params.asid, vpn), page);
                    }
                    return physical_address_lookup(
                        machine,
                        output_address,
                        preferred_exception_return,
                        raise_exception,
                        ret,
                    );
                }
                0b11 => {
                    // Table descriptor
                    TableDescriptor::new(table_entry_2, &params).entry_address
                }
                0b01 => {
                    // Block descriptor
                    let block_desc = BlockDescriptor::new(table_entry_2, &params);
                    let output_address = block_desc.stage_output_address(input_address, &params);
                    if raise_exception {
                        tracing::event!(
                            target: TraceItem::AddressLookup.as_str(),
                            tracing::Level::TRACE,
                            resolved_address = ?output_address
                        );
                    }
                    {
                        let vpn = input_address.0 >> 12;
                        let page = output_address.0 >> 12;
                        let page = page << 12;
                        machine.tlb.insert((params.asid, vpn), page);
                    }
                    return physical_address_lookup(
                        machine,
                        output_address,
                        preferred_exception_return,
                        raise_exception,
                        ret,
                    );
                }
                other => {
                    tracing::debug!(target: TraceItem::AddressLookup.as_str(), "invalid table entry type 0b{other:b}");
                    if raise_exception {
                        fault.statuscode = Fault::Translation;
                        *machine.cpu_state.exit_request.lock().unwrap() =
                            Some(ExitRequest::Abort {
                                fault,
                                preferred_exception_return,
                            });
                    }
                    return false;
                }
            };
            params.level += 1;
            // Block descriptor
            let block_desc = BlockDescriptor::new(base_address.0, &params);
            let output_address = block_desc.stage_output_address(input_address, &params);
            if raise_exception {
                tracing::event!(
                    target: TraceItem::AddressLookup.as_str(),
                    tracing::Level::TRACE,
                    resolved_address = ?output_address
                );
            }
            {
                let vpn = input_address.0 >> 12;
                let page = output_address.0 >> 12;
                let page = page << 12;
                machine.tlb.insert((params.asid, vpn), page);
            }
            physical_address_lookup(
                machine,
                output_address,
                preferred_exception_return,
                raise_exception,
                ret,
            )
        }
        Granule::_16KB | Granule::_64KB => {
            unimplemented!()
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
        4 * 2_u64.pow(get_bits!(machine.cpu_state.id_registers.dczid_el0, off = 0, len = 3) as u32);
    assert!(size <= MAX_ZERO_BLOCK_SIZE);
    let vaddress = align(input_address.0, size);

    for i in 0..size {
        let mut resolved_address = MaybeUninit::uninit();
        if !translate_address(
            machine,
            Address(vaddress + i),
            preferred_exception_return,
            true,
            /* unprivileged */
            false,
            &mut resolved_address,
        ) {
            return false;
        }
        let ResolvedAddress {
                mem_region,
                address_inside_region,
            } =
            // SAFETY: we checked the return value
            unsafe { resolved_address.assume_init() };
        let mem_region = mem_region.unwrap();
        let mem_region = machine
            .memory
            .find_region_mut(mem_region.phys_offset)
            .unwrap();
        let mut exception = MaybeUninit::uninit();
        if !crate::memory::region::ops::memory_region_write_8(
            mem_region,
            address_inside_region,
            0,
            &mut exception,
        ) {
            // SAFETY: write returned false, so this is initialized
            let exception = unsafe { exception.assume_init() };
            *machine.cpu_state.exit_request.lock().unwrap() = Some(exception);
            return false;
        }
    }
    true
}

pub extern "C" fn tlbi(machine: &Armv8AMachine) {
    machine.tlb.clear();
}
