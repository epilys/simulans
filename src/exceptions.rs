// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

//! Architectural exceptions module

#![allow(non_snake_case)]

use bilge::prelude::*;

use crate::{
    cpu_state::{
        ArchMode, DAIFFields, Exception, ExceptionLevel, Mode, SavedProgramStatusRegister, SpSel,
        TranslationControlRegister, PSTATE,
    },
    get_bits,
    memory::Address,
    set_bits, tracing,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AccessType {
    /// Instruction FETCH
    IFETCH,
    /// Software load/store to a General Purpose Register
    GPR,
    /// Software ASIMD extension load/store instructions
    ASIMD,
    /// Software SVE load/store instructions
    SVE,
    /// Software SME load/store instructions
    SME,
    /// Sysop IC
    IC,
    /// Sysop DC (not DC {Z,G,GZ}VA)
    DC,
    /// Sysop DC {Z,G,GZ}VA
    DCZero,
    /// Sysop AT
    AT,
    /// NV2 memory redirected access
    NV2,
    /// Statistical Profiling buffer access
    SPE,
    /// Guarded Control Stack access
    GCS,
    /// Trace Buffer access
    TRBE,
    /// Granule Protection Table Walk
    GPTW,
    /// Access to the HACDBS structure
    HACDBS,
    /// Access to entries in HDBSS
    HDBSS,
    /// Translation Table Walk
    TTW,
}

/// Fault types
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Fault {
    None,
    AccessFlag,
    Alignment,
    Background,
    Domain,
    Permission,
    Translation,
    AddressSize,
    SyncExternal,
    SyncExternalOnWalk,
    SyncParity,
    SyncParityOnWalk,
    GPCFOnWalk,
    GPCFOnOutput,
    AsyncParity,
    AsyncExternal,
    TagCheck,
    Debug,
    TLBConflict,
    BranchTarget,
    HWUpdateAccessFlag,
    Lockdown,
    Exclusive,
    ICacheMaint,
}

impl Fault {
    /// Function that gives the Long-descriptor `FSC` code for types of
    /// [`Fault`]
    ///
    /// `EncodeLDFSC`
    fn encode_ldfsc(&self, level: u8) -> u8 {
        match self {
            Self::AddressSize => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                level & 0b11
            }
            Self::AccessFlag => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                (0b0010 << 2) | (level & 0b11)
            }
            Self::Permission => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                (0b0011 << 2) | (level & 0b11)
            }
            Self::Translation => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                (0b0001 << 2) | (level & 0b11)
            }
            Self::SyncExternal => 0b010000,
            Self::SyncExternalOnWalk => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                (0b0101 << 2) | (level & 0b11)
            }
            Self::SyncParity => 0b011000,
            Self::SyncParityOnWalk => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                0b0111 << 2 | (level & 0b11)
            }
            Self::AsyncParity => 0b011001,
            Self::AsyncExternal => {
                unreachable!()
                // 0b010001
                // assert UsingAArch32()
            }
            Self::TagCheck => {
                // assert IsFeatureImplemented(FEAT_MTE2)
                unimplemented!()
                // 0b010001
            }
            Self::Alignment => 0b100001,
            Self::Debug => 0b100010,
            Self::GPCFOnWalk => {
                assert!([0, 1, 2, 3].contains(&level), "{level}");
                (0b1001 << 2) | (level & 0b11)
            }
            Self::GPCFOnOutput => 0b101000,
            Self::TLBConflict => 0b110000,
            Self::HWUpdateAccessFlag => 0b110001,
            Self::Lockdown => 0b110100,  // IMPLEMENTATION DEFINE
            Self::Exclusive => 0b110101, // IMPLEMENTATION DEFINE
            _other => unreachable!("{_other:?}"),
        }
    }
}

/// The Security state of an execution context
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum SecurityState {
    NonSecure,
    Root,
    Realm,
    Secure,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// Memory access or translation invocation details that steer architectural
/// behavior
pub struct AccessDescriptor {
    pub acctype: AccessType,
    /// Acting EL for the access
    pub el: ExceptionLevel,
    /// Acting Security State for the access
    pub ss: SecurityState,
    // /// Acquire with Sequential Consistency
    // pub acqsc: bool,
    // /// FEAT_LRCPC: Acquire with Processor Consistency
    // pub acqpc: bool,
    // /// Release with Sequential Consistency
    // pub relsc: bool,
    // /// FEAT_LOR: Acquire/Release with limited ordering
    // pub limitedordered: bool,
    /// Access has Exclusive semantics
    pub exclusive: bool,
    // /// FEAT_LSE: Atomic read-modify-write access
    // pub atomicop: bool,
    // /// FEAT_LSE: The modification operation in the 'atomicop' access
    // pub modop: MemAtomicOp,
    // /// Hints the access is non-temporal
    // pub nontemporal: bool,
    /// Read from memory or only require read permissions
    pub read: bool,
    /// Write to memory or only require write permissions
    pub write: bool,
    // /// DC/IC: Cache operation
    // pub cacheop: CacheOp,
    // /// DC/IC: Scope of cache operation
    // pub opscope: CacheOpScope,
    // /// DC/IC: Type of target cache
    // pub cachetype: CacheType,
    // /// FEAT_PAN: The access is subject to PSTATE.PAN
    // pub pan: bool,
    // /// FEAT_TME: Access is part of a transaction
    // pub transactional: bool,
    // /// SVE: Non-faulting load
    // pub nonfault: bool,
    // /// SVE: First-fault load
    // pub firstfault: bool,
    // /// SVE: First-fault load for the first active element
    // pub first: bool,
    // /// SVE: Contiguous load/store not gather load/scatter store
    // pub contiguous: bool,
    // /// SME: Access made by PE while in streaming SVE mode
    // pub streamingsve: bool,
    // /// FEAT_LS64: Accesses by accelerator support loads/stores
    // pub ls64: bool,
    // /// FEAT_LS64: Store with status result
    // pub withstatus: bool,
    // /// FEAT_MOPS: Memory operation (CPY/SET) accesses
    // pub mops: bool,
    // /// FEAT_THE: Read-Check-Write access
    // pub rcw: bool,
    // /// FEAT_THE: Read-Check-Write Software access
    // pub rcws: bool,
    // /// FEAT_THE: Translation table walk access for TTB address
    // pub toplevel: bool,
    // /// FEAT_THE: The corresponding TTBR supplying the TTB
    // pub varange: VARange,
    // /// A32 Load/Store Multiple Data access
    // pub a32lsmd: bool,
    // /// FEAT_MTE2: Access is tag checked
    // pub tagchecked: bool,
    // /// FEAT_MTE: Access targets the tag bits
    // pub tagaccess: bool,
    // /// FEAT_MTE: Accesses that store Allocation tags to Device memory are CONSTRAINED
    // UNPREDICTABLE pub stzgm: bool,
    /// Access represents a Load/Store pair access
    pub ispair: bool,
    // /// FEAT_LRCPC3: Highest address is accessed first
    // pub highestaddressfirst: bool,
    // // FEAT_MPAM: MPAM information
    // pub mpam: MPAMinfo,
}

impl AccessDescriptor {
    /// Create a new [`AccessDescriptor`] with initialised fields
    /// `NewAccDesc`
    pub fn new(privileged: bool, pstate: &PSTATE, acctype: AccessType) -> Self {
        Self {
            acctype,
            el: if !privileged {
                ExceptionLevel::EL0
            } else {
                pstate.EL()
            },
            ss: SecurityState::NonSecure, // TODO SecurityStateAtEL(PSTATE.EL),
            // acqsc: false,
            // acqpc: false,
            // relsc: false,
            // limitedordered: false,
            exclusive: false,
            // rcw: false,
            // rcws: false,
            // atomicop: false,
            // nontemporal: false,
            read: false,
            write: false,
            // pan: false,
            // nonfault: false,
            // firstfault: false,
            // first: false,
            // contiguous: false,
            // streamingsve: false,
            // ls64: false,
            // withstatus: false,
            // mops: false,
            // a32lsmd: false,
            // tagchecked: false,
            // tagaccess: false,
            // stzgm: false,
            // transactional: false,
            // mpam: GenMPAMCurEL(acctype),
            ispair: false,
            // highestaddressfirst: false,
        }
    }
}

/// The allowed error states that can be returned by memory and used by the PE.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ErrorState {
    /// Uncontainable
    UC,
    /// Unrecoverable state
    UEU,
    /// Restartable state
    UEO,
    /// Recoverable state
    UER,
    /// Corrected
    CE,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FaultRecord {
    /// Fault Status
    pub statuscode: Fault,
    /// Details of the faulting access
    pub accessdesc: AccessDescriptor,
    /// Faulting virtual address
    pub vaddress: Address,
    /// Intermediate physical address
    pub ipaddress: FullAddress,
    // /// Granule Protection Check Fault record
    // pub gpcf: GPCFRecord,
    /// Physical address
    pub paddress: FullAddress,
    /// GPC for a stage 2 translation table walk
    pub gpcfs2walk: bool,
    /// Is on a Stage 1 translation table walk
    pub s2fs1walk: bool,
    /// TRUE for a write, FALSE for a read
    pub write: bool,
    /// TRUE for a fault due to tag not accessible at stage 1.
    pub s1tagnotdata: bool,
    /// TRUE for a fault due to `NoTagAccess` permission.
    pub tagaccess: bool,
    /// For translation, access flag and `Permission` faults
    pub level: u8,
    /// IMPLEMENTATION DEFINED syndrome for `External` aborts
    pub extflag: bool,
    /// Is a Stage 2 abort
    pub secondstage: bool,
    /// Stage 2 Permission fault due to `AssuredOnly` attribute
    pub assuredonly: bool,
    /// Stage 2 Permission fault due to `TopLevel`
    pub toplevel: bool,
    /// Fault due to overlay permissions
    pub overlay: bool,
    /// Fault due to dirty state
    pub dirtybit: bool,
    // /// Domain number, AArch32 only
    // pub domain: bits(4),
    /// Incoming error state from memory
    pub merrorstate: ErrorState,
    // /// Fault caused by HDBSS
    // pub hdbssf: bool,
    // /// Watchpoint related fields
    // pub watchptinfo: WatchpointInfo,
    // /// Debug method of entry, from AArch32 only
    // pub debugmoe: bits(4)
}

impl FaultRecord {
    pub fn no_fault(accessdesc: AccessDescriptor, vaddress: Address) -> Self {
        let write = !accessdesc.read && accessdesc.write;
        Self {
            statuscode: Fault::None,
            ipaddress: FullAddress::UNKNOWN,
            paddress: FullAddress::UNKNOWN,
            accessdesc,
            vaddress,
            gpcfs2walk: false,
            s2fs1walk: true,
            write,
            s1tagnotdata: false,
            tagaccess: false,
            level: 0,
            extflag: false,
            secondstage: false,
            assuredonly: false,
            toplevel: false,
            overlay: false,
            dirtybit: false,
            merrorstate: ErrorState::UER,
        }
    }

    /// Returns true if the IPA is reported for the abort
    pub fn ipa_valid(&self) -> bool {
        debug_assert!(
            !matches!(self.statuscode, Fault::None),
            "{:?}",
            self.statuscode
        );
        // if self.gpcf.gpf != GPCF_None then
        // return self.secondstage;
        if self.s2fs1walk {
            matches!(
                self.statuscode,
                Fault::AccessFlag | Fault::Permission | Fault::Translation | Fault::AddressSize
            )
        } else if self.secondstage {
            matches!(
                self.statuscode,
                Fault::AccessFlag | Fault::Translation | Fault::AddressSize
            )
        } else {
            false
        }
    }
}

#[bitsize(49)]
#[derive(Copy, Clone, Default, FromBits, DebugBits)]
/// [`ExceptionRecord`] field.
pub struct IssType {
    /// `iss` field
    pub iss: u25,
    /// `iss2` field
    pub iss2: u24,
}

impl IssType {
    pub fn empty() -> Self {
        Self::new(u25::new(0), u24::new(0))
    }

    /// Creates an exception syndrome value and updates the virtual address for
    /// Abort and Watchpoint exceptions taken to an Exception level using
    /// `AArch64`.
    ///
    /// `AArch64.FaultSyndrome`
    pub fn fault_syndrome(exceptype: Exception, fault: FaultRecord) -> Self {
        debug_assert!(
            !matches!(fault.statuscode, Fault::None),
            "{:?}",
            fault.statuscode
        );
        let mut isstype = Self::empty();

        let d_side: bool = matches!(
            exceptype,
            Exception::DataAbort
                | Exception::NV2DataAbort
                | Exception::Watchpoint
                | Exception::NV2Watchpoint
        );
        if d_side {
            isstype.set_iss2_bit(8, matches!(fault.accessdesc.acctype, AccessType::GCS));

            // if matches!(exceptype , Exception::Watchpoint, Exception::NV2Watchpoint) {
            //     isstype.iss<23:0> = WatchpointRelatedSyndrome(fault);
            // }
            // if IsFeatureImplemented(FEAT_LS64) && fault.accessdesc.ls64 then
            //     if (fault.statuscode IN {Fault_AccessFlag, Fault_Translation,
            // Fault_Permission}) then         (isstype.iss2,
            // isstype.iss<24:14>) = LS64InstructionSyndrome();
            // elsif (IsSecondStage(fault) && !fault.s2fs1walk &&
            //     (!IsExternalSyncAbort(fault) ||
            //      (!IsFeatureImplemented(FEAT_RAS) && fault.accessdesc.acctype ==
            // AccessType_TTW &&       boolean IMPLEMENTATION_DEFINED "ISV on
            // second stage translation table walk"))) then     isstype.iss<24:
            // 14> = LSInstructionSyndrome(); if IsFeatureImplemented(FEAT_NV2)
            // && fault.accessdesc.acctype == AccessType_NV2 then     isstype.
            // iss<13> = '1'; // Fault is generated by use of VNCR_EL2
            // if (IsFeatureImplemented(FEAT_LS64) &&
            // fault.statuscode IN {Fault_AccessFlag, Fault_Translation, Fault_Permission})
            // then isstype.iss<12:11> = GetLoadStoreType();
            isstype.set_iss_bit(
                8,
                matches!(
                    fault.accessdesc.acctype,
                    AccessType::DC | AccessType::IC | AccessType::AT
                ),
            );
            if matches!(
                fault.accessdesc.acctype,
                AccessType::DC | AccessType::IC | AccessType::AT
            ) {
                isstype.set_iss_bit(6, true);
            } else {
                isstype.set_iss_bit(6, fault.write);
            }

            if matches!(fault.statuscode, Fault::Permission) {
                isstype.set_iss2_bit(5, fault.dirtybit);
                isstype.set_iss2_bit(6, fault.overlay);
                if get_bits!(u32::from(isstype.iss()), off = 24, len = 1) == 0 {
                    isstype.set_iss_bit(21, fault.toplevel);
                }
                isstype.set_iss2_bit(7, fault.assuredonly);
                isstype.set_iss2_bit(9, fault.tagaccess);
                isstype.set_iss2_bit(10, fault.s1tagnotdata);
            }
        } else if matches!(
            (fault.accessdesc.acctype, fault.statuscode),
            (AccessType::IFETCH, Fault::Permission)
        ) {
            isstype.set_iss2_bit(5, fault.dirtybit);
            isstype.set_iss_bit(21, fault.toplevel);
            isstype.set_iss2_bit(7, fault.assuredonly);
            isstype.set_iss2_bit(6, fault.overlay);
        }
        // isstype.set_iss2_bit(11, fault.hdbssf);
        // if IsExternalAbort(fault) then isstype.iss<9> = fault.extflag;
        isstype.set_iss_bit(7, fault.s2fs1walk);
        isstype.set_iss_bits(0, 6, fault.statuscode.encode_ldfsc(fault.level).into());
        isstype
    }

    pub fn set_iss_bits(&mut self, lsb: u8, len: u8, value: u16) {
        assert!(lsb + len < 25, "lsb = {lsb}, len = {len}");
        let value = u32::from(value);
        let previous_value = u32::from(self.iss());
        let new_value = set_bits!(previous_value, off = lsb, len = len, val = value);
        self.set_iss(u25::new(new_value));
    }

    fn set_iss_bit(&mut self, bit: u8, value: bool) {
        assert!(bit < 25, "{bit}");
        if value {
            self.set_iss(u25::new(u32::from(self.iss()) | (1 << bit)));
        } else {
            self.set_iss(u25::new(u32::from(self.iss()) & !(1 << bit)));
        }
    }

    fn set_iss2_bit(&mut self, bit: u8, value: bool) {
        assert!(bit < 24, "{bit}");
        if value {
            self.set_iss2(u24::new(u32::from(self.iss2()) | (1 << bit)));
        } else {
            self.set_iss2(u24::new(u32::from(self.iss2()) & !(1 << bit)));
        }
    }
}

/// [`ExceptionRecord`] field.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct FullAddress {
    /// PA space
    pub paspace: PASpace,
    /// 56 bits
    pub address: Address,
}

impl FullAddress {
    pub const UNKNOWN: Self = Self {
        paspace: PASpace::UNKNOWN,
        address: Address(0x0),
    };
}

/// Physical address spaces
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PASpace {
    /// Unknown
    UNKNOWN = 0,
    /// Root
    Root,
    /// System Agent,
    SystemAgent,
    /// Non-Secure Protected,
    NonSecureProtected,
    /// Reserved
    NA6,
    /// Reserved
    NA7,
    /// Realm
    Realm,
    /// Secure
    Secure,
    /// Non-Secure
    NonSecure,
}

/// <https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/shared-exceptions-exceptions?lang=en#shared.exceptions.exceptions.ExceptionRecord>
#[derive(Copy, Clone, Debug)]
pub struct ExceptionRecord {
    /// Exception class
    pub exceptype: Exception,
    /// Syndrome record
    pub syndrome: IssType,
    /// Physical fault address
    pub paddress: FullAddress,
    /// Virtual fault address
    pub vaddress: Address,
    /// Validity of Intermediate Physical fault address
    pub ipavalid: bool,
    /// Validity of Physical fault address
    pub pavalid: bool,
    /// Intermediate Physical fault address space
    pub NS: bool,
    /// Intermediate Physical fault address (56 bits)
    pub ipaddress: Address,
    /// Trapped SVC or SMC instruction
    pub trappedsyscallinst: bool,
}

impl ExceptionRecord {
    /// Return a blank exception syndrome record for an exception of the given
    /// type.
    ///
    /// <https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/shared-exceptions-exceptions?lang=en#shared.exceptions.exceptions.ExceptionSyndrome>
    pub fn exception_syndrome(exceptype: Exception) -> Self {
        Self {
            exceptype,
            syndrome: IssType::empty(),
            vaddress: Address(0x0),
            ipavalid: false,
            pavalid: false,
            NS: false,
            ipaddress: Address(0x0),
            paddress: FullAddress::UNKNOWN,
            trappedsyscallinst: false,
        }
    }

    /// `AArch64.AbortSyndrome`
    ///
    /// Creates an exception syndrome record for Abort and Watchpoint exceptions
    /// from an `AArch64` translation regime.
    pub fn abort_syndrome(exceptype: Exception, fault: FaultRecord) -> Self {
        let mut except = Self::exception_syndrome(exceptype);
        except.pavalid = true;
        except.syndrome = IssType::fault_syndrome(exceptype, fault);
        except.vaddress = fault.vaddress;

        if fault.ipa_valid() {
            except.ipavalid = true;
            except.NS = matches!(fault.ipaddress.paspace, PASpace::NonSecure);
            except.ipaddress = fault.ipaddress.address;
        } else {
            except.ipavalid = false;
        }
        except
    }
}

/// Raise an "Undefined" exception
///
/// [AArch64.Undefined](https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/aarch64-exceptions-traps?lang=en#aarch64.exceptions.traps.AArch64.Undefined)
pub extern "C" fn aarch64_undefined(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
) {
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, "AArch64.Undefined");
    let current_el = machine.cpu_state.PSTATE().EL();

    let route_to_el2 =
        matches!(current_el, ExceptionLevel::EL0) && machine.cpu_state.EL2_enabled() && {
            // HCR_EL2.TGE == '1';
            machine.cpu_state.control_registers.hcr_el2 & (1 << 27) > 0
        };
    let vect_offset = Address(0x0);
    let except = ExceptionRecord::exception_syndrome(Exception::Uncategorized);

    if current_el as u32 > ExceptionLevel::EL1 as u32 {
        aarch64_take_exception(
            machine,
            current_el,
            except,
            preferred_exception_return,
            vect_offset,
        );
    } else if route_to_el2 {
        aarch64_take_exception(
            machine,
            ExceptionLevel::EL2,
            except,
            preferred_exception_return,
            vect_offset,
        );
    } else {
        aarch64_take_exception(
            machine,
            ExceptionLevel::EL1,
            except,
            preferred_exception_return,
            vect_offset,
        );
    }
}

/// Returns the Exception Class and Instruction Length fields to be reported in
/// `ESR` `AArch64.ExceptionClass`
fn exception_class(
    exceptype: Exception,
    pstate: &PSTATE,
    target_el: ExceptionLevel,
) -> (u32, bool) {
    let mut ec = match exceptype {
        Exception::IRQ | Exception::FIQ => unreachable!(),
        Exception::Uncategorized => 0x00,
        Exception::WFxTrap => 0x01,
        // Exception::AdvSIMDFPAccessTrap => 0x07,
        // Exception::FPIDTrap => 0x08,
        // Exception::PACTrap => 0x09,
        // Exception::LDST64BTrap => 0x0A,
        // Exception::TSTARTAccessTrap => 0x1B,
        // Exception::GPC => 0x1E,
        // Exception::BranchTarget => 0x0D,
        Exception::IllegalState => 0x0E,
        Exception::SupervisorCall => 0x11,
        Exception::HypervisorCall => 0x12,
        Exception::MonitorCall => 0x13,
        Exception::SystemRegisterTrap => 0x18,
        // Exception::SystemRegister128Trap => 0x14,
        // Exception::SVEAccessTrap => 0x19,
        Exception::ERetTrap => 0x1A,
        Exception::PACFail => 0x1C,
        // Exception::SMEAccessTrap => 0x1D,
        Exception::InstructionAbort => 0x20,
        Exception::PCAlignment => 0x22,
        Exception::DataAbort => 0x24,
        Exception::NV2DataAbort => 0x25,
        Exception::SPAlignment => 0x26,
        // Exception::MemCpyMemSet => 0x27,
        // Exception::GCSFail => 0x2D,
        Exception::FPTrappedException => 0x28,
        Exception::SError => 0x2F,
        Exception::Breakpoint => 0x30,
        Exception::SoftwareStep => 0x32,
        Exception::Watchpoint => 0x34,
        Exception::NV2Watchpoint => 0x35,
        Exception::SoftwareBreakpoint => 0x38,
        // Exception::Profiling => 0x3D,
    };
    if [0x20, 0x24, 0x30, 0x32, 0x34].contains(&ec) && target_el == pstate.EL() {
        ec += 1;
    }
    if [0x11, 0x12, 0x13, 0x28, 0x38].contains(&ec) {
        ec += 4;
    }
    (ec, true)
}

/// Report syndrome information for exception taken to `AArch64` state
///
/// `AArch64.ReportException`
fn aarch64_report_exception(
    machine: &mut crate::machine::Armv8AMachine,
    except: &ExceptionRecord,
    target_el: ExceptionLevel,
) {
    let (ec, il) = exception_class(except.exceptype, &machine.cpu_state.PSTATE(), target_el);
    let iss = except.syndrome.iss();
    let iss2 = except.syndrome.iss2();
    let esr = //0  <63:56>
             u64::from(iss2) << 32 // <55:32>
             | u64::from(get_bits!(ec, off = 0, len = 6)) << 26 // ec<5:0>  <31:26>
             | u64::from(il) << 25 // <25>
             | u64::from(iss); // <24:0>
    machine.cpu_state.set_esr_elx(esr, target_el);

    if [
        Exception::InstructionAbort,
        Exception::PCAlignment,
        Exception::DataAbort,
        Exception::NV2DataAbort,
        Exception::NV2Watchpoint,
        // Exception::GPC,
        Exception::Watchpoint,
    ]
    .contains(&except.exceptype)
    {
        machine.cpu_state.set_far_elx(except.vaddress.0, target_el);
    } else {
        machine.cpu_state.set_far_elx(0, target_el);
    }
}

/// Prepares machine state to take an exception and updates `pc` with the
/// appropriate exception vector entry.
pub fn aarch64_take_exception(
    machine: &mut crate::machine::Armv8AMachine,
    target_el: ExceptionLevel,
    except: ExceptionRecord,
    preferred_exception_return: Address,
    vect_offset: Address,
) {
    let current_el = machine.cpu_state.PSTATE().EL();

    assert!(machine.cpu_state.have_el(target_el));
    //assert!(!ELUsingAArch32(target_el));
    assert!(target_el as u32 >= current_el as u32);

    let mut adjusted_vect_offset = vect_offset;

    if target_el as u32 > current_el as u32 {
        // Skip aarch32, we don't support it.
        // let lower_32: bool = if target_el == ExceptionLevel::EL3 {
        //     if machine.cpu_state.EL2_enabled() {
        //         ELUsingAArch32(ExceptionLevel::EL2)
        //     } else {
        //         ELUsingAArch32(ExceptionLevel::EL1)
        //     }
        // } else if machine.cpu_state.is_in_host()
        //     && machine.cpu_state.pstate.EL == ExceptionLevel::EL0
        //     && target_el == ExceptionLevel::EL2
        // {
        //     ELUsingAArch32(ExceptionLevel::EL0)
        // } else {
        //     ELUsingAArch32(target_el - 1)
        // };
        let lower_32 = false;
        adjusted_vect_offset += if lower_32 { 0x600_u64 } else { 0x400 };
    } else if matches!(machine.cpu_state.PSTATE().SP(), SpSel::Current) {
        adjusted_vect_offset += 0x200_u64;
    }

    if !matches!(except.exceptype, Exception::IRQ | Exception::FIQ) {
        aarch64_report_exception(machine, &except, target_el);
    }

    // bits(64) spsr = GetPSRFromPSTATE(AArch64_NonDebugState, 64);
    let spsr = machine.cpu_state.psr_from_PSTATE();
    machine.cpu_state.PSTATE_mut().set_EL(target_el);
    machine.cpu_state.PSTATE_mut().set_nRW(ArchMode::_64);
    machine.cpu_state.PSTATE_mut().set_SP(SpSel::Current);

    // SPSR_ELx[] = spsr;
    machine.cpu_state.set_spsr_elx(spsr);

    // ELR_ELx[] = preferred_exception_return;
    machine.cpu_state.set_elr_elx(preferred_exception_return.0);

    machine.cpu_state.PSTATE_mut().set_SS(false);
    // PSTATE.<D,A,I,F> = '1111';
    machine
        .cpu_state
        .PSTATE_mut()
        .set_DAIF(DAIFFields::new(true, true, true, true));
    machine.cpu_state.PSTATE_mut().set_IL(false);

    let vbar_elx = machine.cpu_state.vbar_elx();

    // VBAR_ELx[]<63:11>:vect_offset<10:0>
    machine.pc = set_bits!(
        vbar_elx,
        off = 0,
        len = 11,
        val = get_bits!(adjusted_vect_offset.0, off = 0, len = 11)
    );
    tracing::event!(
        target: tracing::TraceItem::Exception.as_str(),
        tracing::Level::TRACE,
        current_el = ?current_el,
        ?target_el,
        ?vect_offset,
        ?adjusted_vect_offset,
        ?preferred_exception_return,
        vbar = ?tracing::Hex(vbar_elx),
        new_pc = ?Address(machine.pc),
    );
}

/// Convert an SPSR value encoding to an Exception level.
fn EL_from_SPSR(
    machine: &crate::machine::Armv8AMachine,
    spsr: SavedProgramStatusRegister,
) -> Option<ExceptionLevel> {
    if matches!(spsr.nRW(), ArchMode::_64) {
        // AArch64 state
        let el = match spsr.M() {
            Mode::EL0 => ExceptionLevel::EL0,
            Mode::EL1t | Mode::EL1h => ExceptionLevel::EL1,
            Mode::EL1tNV | Mode::EL1hNV => ExceptionLevel::EL2,
            _ => ExceptionLevel::EL2,
        };

        if !machine.cpu_state.have_el(el) {
            // Exception level not implemented
            return None;
        }
        if matches!(spsr.M(), Mode::Undefined) {
            // M<1> must be 0
            return None;
        }

        if matches!(
            (el, spsr.M()),
            (ExceptionLevel::EL0, Mode::EL1h | Mode::EL1hNV)
        ) {
            // for EL0, M<0> must be 0
            return None;
        }

        // elsif IsFeatureImplemented(FEAT_RME) && el != EL3 && effective_nse_ns == '10'
        // then     valid = FALSE;      // Only EL3 valid in Root state
        // elsif el == EL2 && HaveEL(EL3) && !IsSecureEL2Enabled() && SCR_EL3.NS == '0'
        // then     valid = FALSE;      // Unless Secure EL2 is enabled, EL2
        // valid only in Non-secure state
        Some(el)
    } else {
        None
    }
}

/// Check for illegal return
///
/// * To an unimplemented Exception level.
/// * To `EL2` in Secure state, when `SecureEL2` is not enabled.
/// * To `EL0` using `AArch64` state, with `SPSR.M<0>==1`.
/// * To `AArch64` state with `SPSR.M<1>==1`.
/// * To `AArch32` state with an illegal value of `SPSR.M`.
fn illegal_exception_return(
    machine: &crate::machine::Armv8AMachine,
    spsr: SavedProgramStatusRegister,
) -> bool {
    let Some(target_el) = EL_from_SPSR(machine, spsr) else {
        return true;
    };

    // Check for return to higher Exception level
    if target_el as u32 > machine.cpu_state.PSTATE().EL() as u32 {
        return true;
    }

    false
}

/// Set PSTATE based on a `SavedProgramStatusRegister` value
fn set_PSTATE_from_PSR(
    machine: &mut crate::machine::Armv8AMachine,
    spsr: SavedProgramStatusRegister,
    illegal_psr_state: bool,
) {
    if illegal_psr_state {
        machine.cpu_state.PSTATE_mut().set_IL(true);
        // if IsFeatureImplemented(FEAT_SSBS) then PSTATE.SSBS = bit UNKNOWN;
        // if IsFeatureImplemented(FEAT_BTI) then PSTATE.BTYPE = bits(2)
        // UNKNOWN; if IsFeatureImplemented(FEAT_UAO) then PSTATE.UAO =
        // bit UNKNOWN; if IsFeatureImplemented(FEAT_DIT) then
        // PSTATE.DIT = bit UNKNOWN; if IsFeatureImplemented(FEAT_MTE)
        // then PSTATE.TCO = bit UNKNOWN;
        // if IsFeatureImplemented(FEAT_PAuth_LR) then PSTATE.PACM = bit
        // UNKNOWN; if IsFeatureImplemented(FEAT_UINJ) then PSTATE.UINJ
        // = '0';
    } else {
        // State that is reinstated only on a legal exception return
        machine.cpu_state.PSTATE_mut().set_IL(spsr.IL());
        // if IsFeatureImplemented(FEAT_UINJ) then PSTATE.UINJ = spsr<36>;
        // if spsr<4> == '1' then                    // AArch32 state
        //     AArch32.WriteMode(spsr<4:0>);         // Sets PSTATE.EL correctly
        //     if IsFeatureImplemented(FEAT_SSBS) then PSTATE.SSBS = spsr<23>;
        // else                                      // AArch64 state
        machine.cpu_state.PSTATE_mut().set_nRW(ArchMode::_64);
        if let Some(el) = EL_from_SPSR(machine, spsr) {
            machine.cpu_state.PSTATE_mut().set_EL(el);
        }
        machine.cpu_state.PSTATE_mut().set_SP(spsr.SP());
        // if IsFeatureImplemented(FEAT_BTI) then PSTATE.BTYPE = spsr<11:10>;
        // if IsFeatureImplemented(FEAT_SSBS) then PSTATE.SSBS = spsr<12>;
        // if IsFeatureImplemented(FEAT_UAO) then PSTATE.UAO = spsr<23>;
        // if IsFeatureImplemented(FEAT_DIT) then PSTATE.DIT = spsr<24>;
        // if IsFeatureImplemented(FEAT_MTE) then PSTATE.TCO = spsr<25>;
        // if IsFeatureImplemented(FEAT_GCS) then PSTATE.EXLOCK = spsr<34>;
        // if IsFeatureImplemented(FEAT_PAuth_LR) then
        //     PSTATE.PACM = if IsPACMEnabled() then spsr<35> else '0';
    }

    // If PSTATE.IL is set, it is CONSTRAINED UNPREDICTABLE whether the T bit is set
    // to zero or copied from SPSR.
    // if PSTATE.IL == '1' && PSTATE.nRW == '1' {
    //     if ConstrainUnpredictableBool(Unpredictable_ILZEROT) then spsr<5> = '0';
    // }

    // State that is reinstated regardless of illegal exception return
    machine.cpu_state.PSTATE_mut().set_NZCV(spsr.NZCV());
    //if IsFeatureImplemented(FEAT_PAN) then PSTATE.PAN = spsr<22>;
    // if PSTATE.nRW == '1' then                     // AArch32 state
    //     PSTATE.Q         = spsr<27>;
    //     PSTATE.IT        = RestoredITBits(spsr);
    //     ShouldAdvanceIT  = FALSE;
    //     if IsFeatureImplemented(FEAT_DIT) then
    //         PSTATE.DIT = (if (Restarting() || from_aarch64) then spsr<24> else
    // spsr<21>);     PSTATE.GE        = spsr<19:16>;
    //     PSTATE.E         = spsr<9>;
    //     PSTATE.<A,I,F>   = spsr<8:6>;             // No PSTATE.D in AArch32 state
    //     PSTATE.T         = spsr<5>;               // PSTATE.J is RES0
    // else                                          // AArch64 state
    // if (IsFeatureImplemented(FEAT_EBEP) || IsFeatureImplemented(FEAT_SPE_EXC) ||
    //       IsFeatureImplemented(FEAT_TRBE_EXC)) then
    //     PSTATE.PM    = spsr<32>;
    // if IsFeatureImplemented(FEAT_NMI) then PSTATE.ALLINT  = spsr<13>;
    machine.cpu_state.PSTATE_mut().set_DAIF(spsr.DAIF());
}

fn s1_translation_regime(el: ExceptionLevel) -> ExceptionLevel {
    if el != ExceptionLevel::EL0 {
        return el;
    }

    ExceptionLevel::EL1
}

/// Returns the effective Top-byte-ignore value in the `AArch64` stage 1
/// translation regime for `el`.
fn effective_tbi(
    machine: &crate::machine::Armv8AMachine,
    address: Address,
    _is_instr: bool,
    el: ExceptionLevel,
) -> bool {
    debug_assert!(machine.cpu_state.have_el(el), "{el:?}");
    let regime = s1_translation_regime(el);
    match regime {
        ExceptionLevel::EL1 => {
            let tcr_el1 = TranslationControlRegister::from(machine.cpu_state.mmu_registers.tcr_el1);
            if get_bits!(address.0, off = 55, len = 1) == 1 {
                tcr_el1.TBI1()
            } else {
                tcr_el1.TBI0()
            }
        }
        ExceptionLevel::EL2 => {
            // let tcr_el2 =
            // TranslationControlRegister::from(machine.cpu_state.mmu_registers.tcr_el2);
            // tcr_el2.TBI()
            unimplemented!()
        }
        ExceptionLevel::EL3 => {
            // let tcr_el3 =
            // TranslationControlRegister::from(machine.cpu_state.mmu_registers.tcr_el3);
            // tcr_el3.TBI()
            unimplemented!()
        }
        ExceptionLevel::EL0 => unreachable!(),
    }
}

/// Return the MSB number of a virtual address in the stage 1 translation regime
/// for `el`.
fn addr_top(
    machine: &crate::machine::Armv8AMachine,
    address: Address,
    is_instr: bool,
    el: ExceptionLevel,
) -> u32 {
    debug_assert!(machine.cpu_state.have_el(el), "{el:?}");
    if effective_tbi(machine, address, is_instr, el) {
        55
    } else {
        63
    }
}

// Return the virtual address with tag bits removed.
//
// This is typically used when the address will be stored to the program
// counter.
//
// `AArch64.BranchAddr`
fn aarch64_branch_addr(
    machine: &crate::machine::Armv8AMachine,
    vaddress: Address,
    el: ExceptionLevel,
) -> Address {
    let msbit = addr_top(machine, vaddress, true, el);
    if msbit == 63 {
        vaddress
    } else if (matches!(el, ExceptionLevel::EL0 | ExceptionLevel::EL1)/* || IsInHost() */)
        && get_bits!(vaddress.0, off = msbit, len = 1) == 1
    {
        // sign extend:
        let mask = u64::MAX & (2_u64.pow(msbit) - 1);
        Address(mask | vaddress.0)
    } else {
        Address(get_bits!(vaddress.0, off = 0, len = msbit))
    }
}

/// Return from exception
///
/// [AArch64.ExceptionReturn](https://developer.arm.com/documentation/ddi0602/2024-12/Shared-Pseudocode/aarch64-functions-eret?lang=en#AArch64.ExceptionReturn.2)
pub extern "C" fn aarch64_exception_return(
    machine: &mut crate::machine::Armv8AMachine,
    source_pc: Address,
) {
    let mut new_pc = machine.cpu_state.elr_elx();
    let source_el = machine.cpu_state.PSTATE().EL();
    let spsr = machine.cpu_state.spsr_elx();
    // Attempts to change to an illegal state will invoke the Illegal Execution
    // state mechanism
    let illegal_psr_state: bool = illegal_exception_return(machine, spsr);
    set_PSTATE_from_PSR(machine, spsr, illegal_psr_state);
    let target_el = machine.cpu_state.PSTATE().EL();
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, ?source_pc, ?source_el, ?target_el, ?new_pc, "exception return");
    //ClearExclusiveLocal(ProcessorID());
    machine.cpu_state.monitor.clrex();
    //SendEventLocal();
    machine.cpu_state.monitor.event_register = true;
    if machine.cpu_state.PSTATE().IL() {
        new_pc.0 &= !(0b11);
    } else {
        new_pc = aarch64_branch_addr(machine, new_pc, target_el);
    }
    machine.pc = new_pc.0;
}

/// Abort exception handling for translation regime.
///
/// `AArch64.Abort` and mix of `AArch64.DataAbort`
pub fn aarch64_abort(
    machine: &mut crate::machine::Armv8AMachine,
    fault: FaultRecord,
    preferred_exception_return: Address,
) {
    let current_el = machine.cpu_state.PSTATE().EL();

    let route_to_el2 = matches!(current_el, ExceptionLevel::EL0 | ExceptionLevel::EL1)
        && machine.cpu_state.EL2_enabled()
        && {
            // HCR_EL2.TGE == '1';
            machine.cpu_state.control_registers.hcr_el2 & (1 << 27) > 0
            // || (IsFeatureImplemented(FEAT_RME) && fault.gpcf.gpf == GPCF_Fail &&
            // HCR_EL2.GPF == '1') ||
            // (IsFeatureImplemented(FEAT_NV2) &&
            // fault.accessdesc.acctype == AccessType_NV2) ||
            // IsSecondStage(fault)))
        };
    let target_el = if current_el == ExceptionLevel::EL3 {
        current_el
    } else if current_el == ExceptionLevel::EL2 || route_to_el2 {
        ExceptionLevel::EL2
    } else {
        ExceptionLevel::EL1
    };
    let route_to_serr: bool = false; // TODO (IsExternalAbort(fault) && AArch64.RouteToSErrorOffset(target_el));
    let vect_offset = if route_to_serr {
        Address(0x180)
    } else {
        Address(0x0)
    };

    let except = ExceptionRecord::abort_syndrome(Exception::DataAbort, fault);
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, ?target_el, ?vect_offset, ?except, ?preferred_exception_return, "AArch64.Abort");

    aarch64_take_exception(
        machine,
        target_el,
        except,
        preferred_exception_return,
        vect_offset,
    );
}

/// Perform HVC call
///
/// `AArch64.CallHypervisor`
pub fn aarch64_call_hypervisor(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
    immediate: u16,
) {
    if machine.psci_call(immediate) {
        machine.pc = preferred_exception_return.0;
        return;
    }
    let current_el = machine.cpu_state.PSTATE().EL();

    let target_el = if current_el == ExceptionLevel::EL3 {
        current_el
    } else {
        ExceptionLevel::EL2
    };
    assert!(machine.cpu_state.have_el(target_el), "{target_el:?}");
    let vect_offset = Address(0x0);

    let except = ExceptionRecord::exception_syndrome(Exception::Uncategorized);
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, ?target_el, ?vect_offset, ?except, ?preferred_exception_return, "AArch64.CallHypervisor");

    aarch64_take_exception(
        machine,
        target_el,
        except,
        preferred_exception_return,
        vect_offset,
    );
}

/// Perform SVC call
///
/// `AArch64.CallSupervisor`
pub fn aarch64_call_supervisor(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
    immediate: u16,
) {
    let current_el = machine.cpu_state.PSTATE().EL();

    let route_to_el2 = current_el == ExceptionLevel::EL0 && machine.cpu_state.EL2_enabled() && {
        // HCR_EL2.TGE == '1';
        machine.cpu_state.control_registers.hcr_el2 & (1 << 27) > 0
    };

    let target_el = if current_el > ExceptionLevel::EL1 {
        current_el
    } else if route_to_el2 {
        ExceptionLevel::EL2
    } else {
        ExceptionLevel::EL1
    };
    assert!(machine.cpu_state.have_el(target_el), "{target_el:?}");
    let vect_offset = Address(0x0);

    let mut except = ExceptionRecord::exception_syndrome(Exception::SupervisorCall);
    except.syndrome.set_iss_bits(0, 16, immediate);
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, ?target_el, ?vect_offset, ?except, ?preferred_exception_return, "AArch64.CallSupervisor");

    aarch64_take_exception(
        machine,
        target_el,
        except,
        preferred_exception_return,
        vect_offset,
    );
}

/// Software breakpoint
///
/// `AArch64.SoftwareBreakpoint`
pub fn aarch64_software_breakpoint(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
    immediate: u16,
) {
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, immediate = %Address(immediate.into()), "AArch64.SoftwareBreakpoint");
    let current_el = machine.cpu_state.PSTATE().EL();
    let route_to_el2 = matches!(current_el, ExceptionLevel::EL0 | ExceptionLevel::EL1)
        && machine.cpu_state.EL2_enabled()
        && {
            // HCR_EL2.TGE == '1';
            machine.cpu_state.control_registers.hcr_el2 & (1 << 27) > 0
        };

    let target_el = if current_el > ExceptionLevel::EL1 {
        current_el
    } else if route_to_el2 {
        ExceptionLevel::EL2
    } else {
        ExceptionLevel::EL1
    };
    assert!(machine.cpu_state.have_el(target_el), "{target_el:?}");
    let vect_offset = Address(0x0);

    let mut except = ExceptionRecord::exception_syndrome(Exception::SoftwareBreakpoint);
    except.syndrome.set_iss_bits(0, 16, immediate);

    aarch64_take_exception(
        machine,
        target_el,
        except,
        preferred_exception_return,
        vect_offset,
    );
}

/// Take physical FIQ exception
///
/// `AArch64.TakePhysicalFIQException`
pub fn aarch64_take_physical_fiq_exception(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
) {
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, "AArch64.TakePhysicalFIQException");
    let current_el = machine.cpu_state.PSTATE().EL();
    // route_to_el3 = HaveEL(EL3) && SCR_EL3.FIQ == '1'
    let route_to_el2 = matches!(current_el, ExceptionLevel::EL0 | ExceptionLevel::EL1)
        && machine.cpu_state.EL2_enabled()
        && {
            // HCR_EL2.TGE == '1';
            machine.cpu_state.control_registers.hcr_el2 & (1 << 27) > 0
        };

    let target_el = if current_el == ExceptionLevel::EL2 || route_to_el2 {
        ExceptionLevel::EL2
    } else {
        ExceptionLevel::EL1
    };
    assert!(machine.cpu_state.have_el(target_el), "{target_el:?}");
    let vect_offset = Address(0x100);

    let except = ExceptionRecord::exception_syndrome(Exception::FIQ);

    aarch64_take_exception(
        machine,
        target_el,
        except,
        preferred_exception_return,
        vect_offset,
    );
}

/// Take an enabled physical IRQ exception
///
/// `AArch64.TakePhysicalIRQException`
pub fn aarch64_take_physical_irq_exception(
    machine: &mut crate::machine::Armv8AMachine,
    preferred_exception_return: Address,
) {
    tracing::event!(target: tracing::TraceItem::Exception.as_str(), tracing::Level::TRACE, "AArch64.TakePhysicalIRQException");
    let current_el = machine.cpu_state.PSTATE().EL();
    // route_to_el3 = HaveEL(EL3) && SCR_EL3.FIQ == '1'
    let route_to_el2 = matches!(current_el, ExceptionLevel::EL0 | ExceptionLevel::EL1)
        && machine.cpu_state.EL2_enabled()
        && {
            // HCR_EL2.TGE == '1';
            machine.cpu_state.control_registers.hcr_el2 & (1 << 27) > 0
        };

    let target_el = if current_el == ExceptionLevel::EL2 || route_to_el2 {
        ExceptionLevel::EL2
    } else {
        ExceptionLevel::EL1
    };
    assert!(machine.cpu_state.have_el(target_el), "{target_el:?}");
    let vect_offset = Address(0x80);

    let except = ExceptionRecord::exception_syndrome(Exception::IRQ);

    aarch64_take_exception(
        machine,
        target_el,
        except,
        preferred_exception_return,
        vect_offset,
    );
}
