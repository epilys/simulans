// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! MMU - Address Translation

use bilge::prelude::*;

use crate::{
    cpu_state::{
        ExceptionLevel, ExitRequest, Granule, TranslationControlRegister,
        TranslationTableBaseRegister, PSTATE,
    },
    exceptions::{AccessDescriptor, Fault, FaultRecord},
    get_bits,
    machine::Armv8AMachine,
    memory::{AccessType, Address, MemoryRegion},
    set_bits,
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
    #[inline(always)]
    fn alignment_enforced(&self) -> bool {
        let sctlr = self.cpu_state.sctlr_elx();
        sctlr & 0b10 > 0
    }

    /// Determine whether the unaligned access generates an Alignment fault
    ///
    /// `AArch64.UnalignedAccessFaults()`
    #[inline(always)]
    fn unaligned_access_faults(&self, accdesc: &AccessDescriptor) -> bool {
        self.alignment_enforced() || matches!(accdesc.acctype, AccessType::GCS)
    }

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
        let pstate = self.cpu_state.PSTATE();
        let privileged = if unprivileged {
            is_unpriv_access_priv(&pstate)
        } else {
            pstate.EL() != ExceptionLevel::EL0
        };
        let accessdesc = AccessDescriptor {
            read: true,
            ..AccessDescriptor::new(privileged, &pstate, AccessType::GPR)
        };
        if !aligned && self.unaligned_access_faults(&accessdesc) {
            let mut fault = FaultRecord::no_fault(accessdesc, address);
            fault.statuscode = Fault::Alignment;
            return Err(ExitRequest::Abort {
                fault,
                preferred_exception_return,
            });
        }
        if aligned {
            let ResolvedAddress {
                mem_region,
                address_inside_region,
                ..
            } = self.translate_address(address, preferred_exception_return, true, accessdesc)?;
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
                } =
                    self.translate_address(address, preferred_exception_return, true, accessdesc)?;
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
        let pstate = self.cpu_state.PSTATE();
        let privileged = if unprivileged {
            is_unpriv_access_priv(&pstate)
        } else {
            pstate.EL() != ExceptionLevel::EL0
        };
        let accessdesc = AccessDescriptor {
            write: true,
            ..AccessDescriptor::new(privileged, &pstate, AccessType::GPR)
        };
        if !aligned && self.unaligned_access_faults(&accessdesc) {
            let mut fault = FaultRecord::no_fault(accessdesc, address);
            fault.statuscode = Fault::Alignment;
            return Err(ExitRequest::Abort {
                fault,
                preferred_exception_return,
            });
        }
        if aligned {
            let ResolvedAddress {
                mem_region: _,
                address_inside_region,
                physical,
            } = self.translate_address(address, preferred_exception_return, true, accessdesc)?;
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
                } =
                    self.translate_address(address, preferred_exception_return, true, accessdesc)?;
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
        accessdesc: &AccessDescriptor,
        preferred_exception_return: Address,
    ) -> Result<ResolvedAddress<'_>, ExitRequest> {
        let Some(mem_region) = self.memory.find_region(address) else {
            return Err({
                let mut fault = FaultRecord::no_fault(*accessdesc, address);
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
        trace: bool,
        accessdesc: AccessDescriptor,
    ) -> Result<ResolvedAddress<'_>, ExitRequest> {
        let sctlr = self.cpu_state.sctlr_elx();
        if sctlr & 0x1 == 0 {
            // stage 1 MMU disabled
            return self.physical_address_lookup(
                input_address,
                &accessdesc,
                preferred_exception_return,
            );
        }
        let mut fault = FaultRecord::no_fault(accessdesc, input_address);
        let mut ttwstate = TTWState::new(self, &input_address);
        {
            let vpn = input_address.0 >> 12;
            if let Some(page) = self.tlb.get(&(ttwstate.asid, vpn)) {
                fault.level = page.walkstate.level;
                let output_address =
                    Address(page.paddress | get_bits!(input_address.0, off = 0, len = 12));
                if trace {
                    tracing::event!(
                        target: TraceItem::AddressLookup.as_str(),
                        tracing::Level::TRACE,
                        vaddress = ?input_address,
                        resolved_paddress = ?output_address,
                        tlb_hit = true,
                    );
                }
                self.s1_check_permissions(fault, &page.walkstate, &accessdesc, &page.permissions)
                    .map_err(|fault| ExitRequest::Abort {
                        fault,
                        preferred_exception_return,
                    })?;
                return self.physical_address_lookup(
                    output_address,
                    &accessdesc,
                    preferred_exception_return,
                );
            }
        }

        let descriptor = self.s1_walk(
            &mut fault,
            &mut ttwstate,
            &accessdesc,
            input_address,
            preferred_exception_return,
            trace,
        )?;
        if !descriptor.access_flag() {
            fault.statuscode = Fault::AccessFlag;
            return Err(ExitRequest::Abort {
                fault,
                preferred_exception_return,
            });
        }
        let permissions = descriptor.permissions();
        self.s1_check_permissions(fault, &ttwstate, &accessdesc, &permissions)
            .map_err(|fault| ExitRequest::Abort {
                fault,
                preferred_exception_return,
            })?;
        let is_global_entry = ttwstate.regime.has_unprivileged()
            && ttwstate.level == FINAL_LEVEL
            && !descriptor.non_global();
        let output_address = descriptor.stage_output_address(input_address, &ttwstate);
        if trace {
            tracing::event!(
                target: TraceItem::AddressLookup.as_str(),
                tracing::Level::TRACE,
                resolved_address = ?output_address,
            );
        }
        let physical =
            self.physical_address_lookup(output_address, &accessdesc, preferred_exception_return)?;
        {
            let vpn = input_address.0 >> 12;
            let page = output_address.0 >> 12;
            let page = page << 12;
            self.tlb
                .insert(is_global_entry, vpn, page, permissions, ttwstate);
        }
        Ok(physical)
    }

    fn s1_walk(
        &self,
        fault_in: &mut FaultRecord,
        ttwstate: &mut TTWState,
        accessdesc_in: &AccessDescriptor,
        input_address: Address,
        preferred_exception_return: Address,
        trace: bool,
    ) -> Result<Descriptor, ExitRequest> {
        let accessdesc = AccessDescriptor {
            acctype: AccessType::TTW,
            el: accessdesc_in.el,
            ss: accessdesc_in.ss,
            read: true,
            ispair: false,
            write: false,
            exclusive: false,
        };
        let mut fault = FaultRecord::no_fault(accessdesc, input_address);
        let pstate = self.cpu_state.PSTATE();
        let page_table_base_address: Address =
            TranslationTableBaseRegister::from(ttwstate.base_address.0).base_address(ttwstate);

        if trace {
            tracing::event!(
                target: TraceItem::AddressLookup.as_str(),
                tracing::Level::TRACE,
                physical = false,
                address = ?input_address,
                pc = ?Address(self.pc),
                EL = ?pstate.EL(),
                ?ttwstate,
                ?accessdesc_in,
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
                    &accessdesc,
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
                        return Ok(Descriptor::Page(PageDescriptor::new(
                            table_entry_0,
                            ttwstate,
                        )));
                    }
                    0b11 => {
                        // Table descriptor
                        TableDescriptor::new(table_entry_0, ttwstate).entry_address
                    }
                    0b01 => {
                        // Block descriptor
                        return Ok(Descriptor::Block(BlockDescriptor::new(
                            table_entry_0,
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

                let table_entry_1 =
                    read_table_entry!(base_address, IA4KB::idx(input_address.0, ttwstate));
                fault.level = ttwstate.level;
                fault_in.level = ttwstate.level;
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
                        return Ok(Descriptor::Page(PageDescriptor::new(
                            table_entry_1,
                            ttwstate,
                        )));
                    }
                    0b11 => {
                        // Table descriptor
                        TableDescriptor::new(table_entry_1, ttwstate).entry_address
                    }
                    0b01 => {
                        // Block descriptor
                        return Ok(Descriptor::Block(BlockDescriptor::new(
                            table_entry_1,
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

                let table_entry_2 =
                    read_table_entry!(base_address, IA4KB::idx(input_address.0, ttwstate));
                fault.level = ttwstate.level;
                fault_in.level = ttwstate.level;
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
                fault.level = ttwstate.level;
                fault_in.level = ttwstate.level;
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

    /// Checks whether stage 1 access violates permissions of target memory and
    /// returns a fault record
    ///
    /// `J1.1.4.25 AArch64.S1CheckPermissions`
    fn s1_check_permissions(
        &self,
        mut fault: FaultRecord,
        walkstate: &TTWState,
        accdesc: &AccessDescriptor,
        permissions: &Permissions,
    ) -> Result<(), FaultRecord> {
        let s1perms: S1AccessControls = s1_compute_permissions(walkstate, accdesc);
        if matches!(accdesc.acctype, AccessType::IFETCH) {
            if s1perms.overlay && !s1perms.ox {
                fault.statuscode = Fault::Permission;
                fault.overlay = true;
                return Err(fault);
            }
            if !s1perms.x {
                fault.statuscode = Fault::Permission;
                return Err(fault);
            }
        } else if accdesc.read && s1perms.overlay && !s1perms.or {
            fault.statuscode = Fault::Permission;
            fault.overlay = true;
            fault.write = false;
            return Err(fault);
        } else if accdesc.write && s1perms.overlay && !s1perms.ow {
            fault.statuscode = Fault::Permission;
            fault.overlay = true;
            fault.write = true;
            return Err(fault);
        } else if accdesc.read && !s1perms.r {
            fault.statuscode = Fault::Permission;
            fault.write = false;
            return Err(fault);
        } else if accdesc.write && !s1perms.w {
            fault.statuscode = Fault::Permission;
            fault.write = true;
            return Err(fault);
        // } else if (accdesc.write
        //     && accdesc.tagaccess
        //     && walkstate.memattrs.tags == MemTag::CanonicallyTagged)
        // {
        //     fault.statuscode = Fault::Permission;
        //     fault.write = true;
        //     fault.s1tagnotdata = true;
        //     return Err(fault);
        } else if accdesc.write
            && !(walkstate.ha && walkstate.hd)
            && walkstate.pie
            && permissions.ndirty()
        {
            fault.statuscode = Fault::Permission;
            fault.dirtybit = true;
            fault.write = true;
            return Err(fault);
        }
        Ok(())
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

impl Regime {
    /// Returns translation regime based on current exception level
    fn translation_regime(machine: &Armv8AMachine) -> Self {
        let pstate = machine.cpu_state.PSTATE();
        match pstate.EL() {
            ExceptionLevel::EL3 => {
                // if ELUsingAArch32(EL3) then Regime_EL30
                Self::EL3
            }
            ExceptionLevel::EL2 => {
                // if ELIsInHost(EL2) then Regime_EL20
                Self::EL2
            }
            ExceptionLevel::EL1 | ExceptionLevel::EL0 => Self::EL10,
        }
    }

    /// Returns whether a translation regime serves EL0 as well as a higher EL
    fn has_unprivileged(&self) -> bool {
        matches!(self, Self::EL20 | Self::EL10)
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

/// Access Control bits in translation table descriptors
///
/// `J1.3.3.334 Permissions`
#[bitsize(25)]
#[derive(Default, Copy, Clone, TryFromBits, DebugBits)]
pub struct Permissions {
    /// Stage 1 hierarchical access permissions
    pub ap_table: u2,
    /// Stage 1 hierarchical execute-never for single EL regimes
    pub xn_table: bool,
    /// Stage 1 hierarchical privileged execute-never
    pub pxn_table: bool,
    /// Stage 1 hierarchical unprivileged execute-never
    pub uxn_table: bool,
    /// Stage 1 access permissions
    pub ap: u3,
    /// Stage 1 execute-never for single EL regimes
    pub xn: bool,
    /// Stage 1 unprivileged execute-never
    pub uxn: bool,
    /// Stage 1 privileged execute-never
    pub pxn: bool,
    /// Stage 1 privileged indirect permissions
    pub ppi: u4,
    /// Stage 1 unprivileged indirect permissions
    pub upi: u4,
    /// Stage 1 dirty state for indirect permissions scheme
    pub ndirty: bool,
    // /// Stage 2 indirect permissions
    // pub s2pi: u4,
    // /// Stage 2 dirty state
    // pub s2dirty: u1,
    /// Stage 1 overlay permissions index
    pub po_index: u4,
    // /// Stage 2 overlay permissions index
    // pub s2po_index: u4,
    // /// Stage 2 access permissions
    // pub s2ap: u2,
    /// Stage 2 tag access
    // pub s2tag_na: u1,
    // /// Stage 2 extended execute-never
    // pub s2xnx: u1,
    /// Dirty bit management
    pub dbm: bool,
    // /// Stage 2 execute-never
    // pub s2xn: u1,
}

/// Effective access controls defined by stage 1 translation
#[derive(Copy, Default, Clone, Debug)]
pub struct S1AccessControls {
    /// Stage 1 base read permission
    pub r: bool,
    /// Stage 1 base write permission
    pub w: bool,
    /// Stage 1 base execute permission
    pub x: bool,
    /// Stage 1 GCS permission
    pub gcs: bool,
    /// Stage 1 overlay feature enabled
    pub overlay: bool,
    /// Stage 1 overlay read permission
    pub or: bool,
    /// Stage 1 overlay write permission
    pub ow: bool,
    /// Stage 1 overlay execute permission
    pub ox: bool,
    /// Stage 1 write permission implies execute-never
    pub wxn: bool,
}

/// Computes the stage 1 direct base permissions
///
/// `J1.1.4.27 AArch64.S1DirectBasePermissions`
fn s1_direct_base_permissions(
    walkstate: &TTWState,
    accdesc: &AccessDescriptor,
) -> S1AccessControls {
    let mut permissions = walkstate.permissions;

    let mut ur = true;
    let mut uw = true;
    let mut ux = true;
    let mut pr;
    let mut pw;
    let px;

    let mut ret = S1AccessControls {
        r: true,
        w: true,
        x: true,
        gcs: true,
        overlay: true,
        or: true,
        ow: true,
        ox: true,
        wxn: true,
    };
    if permissions.dbm() && walkstate.hd {
        let ap = u8::from(permissions.ap());
        permissions.set_ap(u3::new(set_bits!(ap, off = 2, len = 1, val = 0)));
    }

    if walkstate.regime.has_unprivileged() {
        let ap = u8::from(permissions.ap());
        // Apply leaf permissions
        (pr, pw, ur, uw) = match get_bits!(ap, off = 1, len = 2) {
            // Privileged access
            0b00 => (true, true, false, false),
            // No effect
            0b01 => (true, true, true, true),
            // Read-only, privileged access
            0b10 => (true, false, false, false),
            // Read-only
            0b11 => (true, false, true, false),
            _ => unreachable!(),
        };
        // Apply hierarchical permissions
        (pr, pw, ur, uw) = match u8::from(permissions.ap_table()) {
            // No effect
            0b00 => (pr, pw, ur, uw),
            // Privileged access
            0b01 => (pr, pw, false, false),
            // Read-only
            0b10 => (pr, false, ur, false),
            // Read-only, privileged access
            0b11 => (pr, false, false, false),
            _ => unreachable!(),
        };
        // Locations writable by unprivileged cannot be executed by privileged
        px = !(permissions.pxn() || permissions.pxn_table() || uw);
        ux = !(permissions.uxn() || permissions.uxn_table());
    } else {
        // Apply leaf permissions
        (pr, pw) = if get_bits!(u8::from(permissions.ap()), off = 2, len = 1) == 0 {
            // No effect
            (true, true)
        } else {
            // Read-only
            (true, false)
        };
        // Apply hierarchical permissions
        (pr, pw) = if get_bits!(u8::from(permissions.ap_table()), off = 1, len = 1) == 0 {
            // No effect
            (pr, pw)
        } else {
            // Read-only
            (pr, false)
        };
        px = !(permissions.xn() || permissions.xn_table());
    }
    let (r, w, x) = if accdesc.el == ExceptionLevel::EL0 {
        (ur, uw, ux)
    } else {
        (pr, pw, px)
    };
    // Compute WXN value
    let wxn = walkstate.wxn && w && x;

    ret.r = r;
    ret.w = w;
    ret.x = x;
    ret.gcs = false;
    ret.wxn = wxn;
    ret.overlay = true;

    ret
}

/// Computes the overall stage 1 permissions
///
/// `J1.1.4.26 AArch64.S1ComputePermissions`
fn s1_compute_permissions(walkstate: &TTWState, accdesc: &AccessDescriptor) -> S1AccessControls {
    // constant Permissions permissions = walkstate.permissions;
    let mut s1perms = if walkstate.pie {
        todo!()
        // s1_indirect_base_permissions(walkstate, accdesc)
    } else {
        s1_direct_base_permissions(walkstate, accdesc)
    };
    s1perms.overlay = false;
    // if accdesc.el == ExceptionLevel::EL0 && !s1_e0_po_enabled(regime,
    // walkparams.nv1) {     s1perms.overlay = false;
    // if accdesc.el != ExceptionLevel::EL0 && !s1_po_enabled(regime) {
    //     s1perms.overlay = false;
    // }
    if s1perms.overlay {
        todo!();
        // let s1overlay_perms = s1_overlay_permissions(regime, walkstate,
        // accdesc); s1perms.or = s1overlay_perms.or;
        // s1perms.ow = s1overlay_perms.ow;
        // s1perms.ox = s1overlay_perms.ox;
    }
    if s1perms.overlay && s1perms.wxn && s1perms.ox {
        // WXN removes overlay write permission if overlay execute permission is not
        // removed.
        s1perms.ow = false;
    } else if s1perms.wxn {
        // In the absence of overlay permissions, if WXN is enabled and both W and X
        // permission are granted, the X permission is removed.
        s1perms.x = false;
    }
    s1perms
}

#[derive(Copy, Clone, Debug)]
/// Translation table walk state
pub struct TTWState {
    #[allow(dead_code)]
    va_range: VARange,
    regime: Regime,
    pub asid: u16,
    level: u8,
    granule: Granule,
    base_address: Address,
    pie: bool,
    ds: bool,
    #[allow(dead_code)]
    non_global: bool,
    /// `TCR_ELx.HA`
    ha: bool,
    /// `TCR_ELx.HD`
    hd: bool,
    /// `SCTLR_ELx.WXN / SCTLR.WXN or HSCTLR.WXN`
    wxn: bool,
    permissions: Permissions,
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
        let regime = Regime::translation_regime(machine);
        let permissions = Permissions::default();
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

        let s1startlevel = {
            // Determine initial lookup level
            // `AArch64.S1StartLevel`
            // Input Address size
            let iasize = 64 - tsz;
            let granulebits = granule.bits();
            let descsizelog2 = 3; //if d128 { 4 } else { 3 };
            let stride = granulebits - descsizelog2;

            FINAL_LEVEL - (((iasize - 1) - granulebits) / stride)
        };
        // if walkparams.d128 == '1' then
        // s1startlevel = s1startlevel + UInt(walkparams.skl);
        Self {
            non_global: regime.has_unprivileged(),
            level: s1startlevel,
            va_range,
            asid,
            regime,
            base_address: ttbr,
            granule,
            permissions,
            ds,
            pie: false,
            ha: tcr.HA(),
            hd: tcr.HD(),
            wxn: get_bits!(machine.cpu_state.sctlr_elx(), off = 19, len = 1) == 1,
        }
    }

    /// Apply output permissions encoded in stage 1 page/block descriptors
    ///
    /// `J1.1.4.67 AArch64.S1ApplyOutputPerms`
    fn s1_apply_output_perms(&mut self, descriptor: u64) {
        let ap = u8::from(self.permissions.ap());
        // if regime == Regime_EL10 && EL2Enabled() && walkparams.nv1 == '1' {
        //     permissions.ap<2:1> = descriptor<7>:'0';
        //     permissions.pxn = descriptor<54>;
        // } else if  HasUnprivileged(regime) {
        if self.regime.has_unprivileged() {
            // self.permissions.ap<2:1> = descriptor<7:6>;
            self.permissions.set_ap(u3::new(set_bits!(
                ap,
                off = 1,
                len = 2,
                val = get_bits!(descriptor, off = 6, len = 2) as u8
            )));
            self.permissions
                .set_uxn(get_bits!(descriptor, off = 54, len = 1) == 1);
            self.permissions
                .set_pxn(get_bits!(descriptor, off = 53, len = 1) == 1);
        } else {
            // permissions.ap<2:1> = descriptor<7>:'1';
            self.permissions.set_ap(u3::new(set_bits!(
                ap,
                off = 1,
                len = 2,
                val = (get_bits!(descriptor, off = 7, len = 1) << 1) as u8 | 1
            )));
            self.permissions
                .set_xn(get_bits!(descriptor, off = 54, len = 1) == 1);
        }
    }

    /// Apply hierarchical permissions encoded in stage 1 table descriptors
    ///
    /// `J1.1.4.68 AArch64.S1ApplyTablePerms`
    fn s1_apply_table_perms(&mut self, descriptor: u64) {
        let prev_ap_table: u8 = self.permissions.ap_table().into();
        if self.regime.has_unprivileged() {
            let ap_table = get_bits!(descriptor, off = 61, len = 2) as u8;
            let uxn_table = get_bits!(descriptor, off = 60, len = 1) == 1;
            let pxn_table = get_bits!(descriptor, off = 59, len = 1) == 1;
            self.permissions
                .set_ap_table(u2::new(prev_ap_table | ap_table));
            let prev_uxn_table = self.permissions.uxn_table();
            self.permissions.set_uxn_table(prev_uxn_table | uxn_table);
            let prev_pxn_table = self.permissions.pxn_table();
            self.permissions.set_pxn_table(prev_pxn_table | pxn_table);
        } else {
            let ap_table = (get_bits!(descriptor, off = 62, len = 1) as u8) << 1;
            let xn_table = get_bits!(descriptor, off = 60, len = 1) == 1;
            self.permissions
                .set_ap_table(u2::new(prev_ap_table | ap_table));
            let prev_xn_table = self.permissions.xn_table();
            self.permissions.set_xn_table(prev_xn_table | xn_table);
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
    let accessdesc = AccessDescriptor::new(false, &machine.cpu_state.PSTATE(), AccessType::DCZero);

    let double_words = size / 8;
    let bytes = size % 8;
    for _ in 0..double_words {
        if let Err(err) = machine.mem_write(
            address,
            &0_u64.to_le_bytes(),
            false,
            preferred_exception_return,
        ) {
            *machine.cpu_state.exit_request.lock().unwrap() = Some(err);
            return false;
        }
        address = Address(address.0 + 8);
    }
    for _ in 0..bytes {
        let ResolvedAddress {
            mem_region: _,
            address_inside_region,
            physical,
        } = match machine.translate_address(address, preferred_exception_return, true, accessdesc) {
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
