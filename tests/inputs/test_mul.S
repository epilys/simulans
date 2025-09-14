.include "tests/inputs/helpers.S.inc"

movq x0, 0xbeef
movq x1, 0x42
movq x2, 0xacabacab

msub w3, w0, w1, w2
msub x4, x0, x1, x2

msub x5, x0, x1, xzr
mneg x6, x0, x1

umulh x7, x0, x2

write_to_tube w30, x29
