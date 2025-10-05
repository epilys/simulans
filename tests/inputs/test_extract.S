.include "tests/inputs/helpers.S.inc"

mov x26, #0x3f
movq x21, 0x307715440000
extr    w18, w26, w21, #0
extr    w19, w26, w21, #8
extr    x20, x26, x21, #0
extr    x21, x26, x21, #8

write_to_tube w30, x29
