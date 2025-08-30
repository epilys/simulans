.include "tests/inputs/helpers.S.inc"

movq x5, 0x40086000
movq x6, 0x40086000
movz x2, #0x0
cmp x5, x6
b.cs carry_set
b quit

carry_set:
movq x2, 0x1

quit:
write_to_tube w30, x29
