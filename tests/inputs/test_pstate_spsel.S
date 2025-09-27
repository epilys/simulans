.include "tests/inputs/helpers.S.inc"

// Set x1 to SP_EL1
mov x1, sp

// Set to SP_EL0
msr SpSel, #0
mov x2, sp
// Set to Current (i.e. SP_EL1)
msr SpSel, #1
mov x3, sp
quit:
  write_to_tube w30, x29
