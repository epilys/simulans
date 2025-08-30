.include "tests/inputs/helpers.S.inc"

msr NZCV, xzr

movz x0, 0x1
movz x1, 0x2

cmp x0, x1
mrs x8, NZCV
msr NZCV, xzr

cmp x1, x0
mrs x9, NZCV
msr NZCV, xzr

cmp xzr, xzr
mrs x10, NZCV

write_to_tube w30, x29
