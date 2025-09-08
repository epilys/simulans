.include "tests/inputs/helpers.S.inc"

movq x0, 0xdeadbeef,
movq x1, 0xdeadbeefdeadbeef,
fmov d0, x1
rev w2, w0
rev32 v0.8b, v0.8b
fmov x3, d0

write_to_tube w30, x29
