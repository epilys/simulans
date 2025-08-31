.include "tests/inputs/helpers.S.inc"

  mov x0, xzr
  adr x0, quit
  msr elr_el1, x0
  eret
  nop

quit:
  write_to_tube w30, x29
