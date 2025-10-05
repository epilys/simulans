.include "tests/inputs/helpers.S.inc"

movq x0, 0b00000000000000000000000000000000
movq x1, 0b00000000000000001000000000000000

clz x2, x0
clz x3, x1

clz w4, w0
clz w5, w1

movq x6, 0b11000000000000000000000000000000

cls x7, x6
cls w8, w6
cls w9, w0
cls x10, x1

movq x6, 0xffffffffffffffff
cls x11, x6

// [ref:FEAT_CSSC]
// cnt x9, x6
// cnt w10, w6
// cnt w11, w1

write_to_tube w30, x29
