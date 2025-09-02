.include "tests/inputs/helpers.S.inc"

mrs x1, CNTFRQ_EL0
msr CNTP_TVAL_EL0, x1
mov x0, 1
msr CNTP_CTL_EL0, x0
write_to_tube w30, x29
