// SPDX-License-Identifier: EUPL-1.2 OR GPL-3.0-or-later
// Copyright Contributors to the simulans project.

use std::num::NonZero;

use simulans::{
    cpu_state::{ExceptionLevel, ExitRequest},
    exceptions::{
        AccessDescriptor, AccessType, ErrorState, Fault, FaultRecord, FullAddress, PASpace,
        SecurityState,
    },
    main_loop,
    memory::{Address, MemorySize},
};

#[macro_use]
mod utils;

#[test_log::test]
fn test_mmu_4k() {
    const TEST_INPUT: &[u8] = include_bytes!("./inputs/test_mmu_4k.bin");
    const TEST_INPUT_ABORT: &[u8] = include_bytes!("./inputs/test_mmu_abort.bin");

    utils::disas(TEST_INPUT, 0);
    const MEMORY_SIZE: MemorySize = MemorySize(NonZero::new(MemorySize::MiB.get() * 1024).unwrap());
    let entry_point = Address(0x02e000000);
    {
        let mut machine = utils::make_test_machine(MEMORY_SIZE, entry_point);
        machine.cpu_state.PSTATE_mut().set_EL(ExceptionLevel::EL1);
        // [ref:TODO]: add address translate instructions

        main_loop(&mut machine, entry_point, TEST_INPUT).unwrap();
        assert_eq!(
            machine
                .cpu_state
                .exit_request
                .lock()
                .unwrap()
                .take()
                .unwrap(),
            ExitRequest::Poweroff
        );
        let mut jit = simulans::jit::Jit::new();

        let mut abort_code = TEST_INPUT_ABORT.to_vec();
        if abort_code.len() < TEST_INPUT.len() {
            // Overwrite previous code just in case
            let diff = TEST_INPUT.len() - abort_code.len();
            abort_code.extend(std::iter::repeat_n(0, diff));
        }
        machine.load_code(&abort_code, entry_point).unwrap();
        machine.pc = entry_point.0;
        let mut func = machine.lookup_block_func;
        while machine.cpu_state.exit_request.lock().unwrap().is_none() {
            func = (func.0)(&mut jit, &mut machine);
        }
        assert_eq!(
            machine.cpu_state.exit_request.lock().unwrap().take(),
            Some(ExitRequest::Abort {
                fault: FaultRecord {
                    statuscode: Fault::Translation,
                    accessdesc: AccessDescriptor {
                        acctype: AccessType::TTW,
                        el: ExceptionLevel::EL1,
                        ss: SecurityState::NonSecure,
                        exclusive: false,
                        read: false,
                        write: false,
                        ispair: false,
                    },
                    vaddress: Address(0xacab),
                    ipaddress: FullAddress {
                        paspace: PASpace::UNKNOWN,
                        address: Address(0x0),
                    },
                    paddress: FullAddress {
                        paspace: PASpace::UNKNOWN,
                        address: Address(0x0),
                    },
                    gpcfs2walk: false,
                    s2fs1walk: true,
                    write: false,
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
                },
                preferred_exception_return: Address(0x2e000010),
            },)
        );
    }
}
