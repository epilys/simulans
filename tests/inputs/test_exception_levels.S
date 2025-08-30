.include "tests/inputs/helpers.S.inc"

  mov x0, #1
  orr x0, x0, #2
  orr x0, x0, #4
  orr x0, x0, #8
  orr x0, x0, #0x100
  orr x0, x0, #0x400
  orr x0, x0, #0x800
  msr scr_el3, x0
  orr w0, wzr, #8
  orr x0, x0, #0x10
  orr x0, x0, #0x80000000
  msr hcr_el2, x0
  mrs x0, midr_el1
  msr vpidr_el2, x0
  mrs x0, mpidr_el1
  msr vmpidr_el2, x0
  msr vttbr_el2, xzr
  msr sctlr_el2, xzr
  msr sctlr_el1, xzr
  mov x0, xzr
  adr x0, quit
  msr elr_el3, x0
  eret
  nop

quit:
  write_to_tube w30, x29
