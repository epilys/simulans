.include "tests/inputs/helpers.S.inc"

  bl foobar
  b quit
foobar:
  sub sp, sp, #0x10
  str w0, [sp, #8]
  ldr w8, [sp, #8]
  mov w10, #2
  sdiv w9, w8, w10
  mul w9, w9, w10
  subs w8, w8, w9
  cbnz w8, .LBB0_2
  b .LBB0_1
.LBB0_1:
  ldr w9, [sp, #8]
  mov w8, #2
  mul w8, w8, w9
  str w8, [sp, #0xc]
  b .LBB0_3
.LBB0_2:
  ldr w8, [sp, #8]
  ldr w9, [sp, #8]
  mul w8, w8, w9
  str w8, [sp, #0xc]
  b .LBB0_3
.LBB0_3:
  ldr w0, [sp, #0xc]
  add sp, sp, #0x10
  ret
quit:
  nop
  write_to_tube w30, x29
