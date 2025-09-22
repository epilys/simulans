.include "tests/inputs/helpers.S.inc"

.macro _daif_local_irq_enable
  msr daifclr, #3
.endm

.macro _daif_local_irq_disable
  msr daifset, #3
.endm

  mrs x0, CurrentEL
  mrs x1, DAIF
  msr DAIFClr, #7 // 0b0111
  mrs x2, DAIF
  msr DAIFSet, #7 // 0b0111
  mrs x3, DAIF
  msr DAIFClr, #15 // 0b1111
  msr DAIFSet, #5 // 0b0101
  mrs x4, DAIF
  msr DAIFClr, #1 // 0b0001
  mrs x5, DAIF

  mov x6, 0xf << 6
  msr DAIF, x6
  mrs x6, DAIF
  _daif_local_irq_enable
  mrs x7, DAIF
  _daif_local_irq_disable
  mrs x8, DAIF
  mov x9, 0b1010 << 6
  msr DAIF, x9
  mrs x9, DAIF
quit:
  write_to_tube w30, x29
