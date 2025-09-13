.include "tests/inputs/helpers.S.inc"

movi v0.8b, #0x80
movi v1.4h, #1
movi v2.4h, #1, lsl #8
movi v3.8h, #1, lsl #8
movi v4.2s, #1, lsl #24
movi v5.2s, #1, msl #16

write_to_tube w30, x29
