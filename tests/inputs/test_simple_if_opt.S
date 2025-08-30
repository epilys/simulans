.include "tests/inputs/helpers.S.inc"

  bl foobar
  b quit
foobar:
  mul     w8, w0, w0
  lsl     w9, w0, #1
  tst     w0, #0x1
  csel    w0, w9, w8, eq
  ret
quit:
  nop
  write_to_tube w30, x29
