.include "tests/inputs/helpers.S.inc"

movq x0, 0xF0CACC1A
movl x1, 0xBEEF
movz    x2, #0x0, lsl #48
movk    x2, #0x0, lsl #32
movk    x2, #0x8080, lsl #16
movk    x2, #0x3519
write_to_tube w30, x29
