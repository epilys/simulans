.include "tests/inputs/helpers.S.inc"

movq x1, 0x40095020
movq x2, 0x1000000
adds x0, x1, x2
cset w8, cs
write_to_tube w30, x29
