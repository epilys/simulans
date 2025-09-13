.include "tests/inputs/helpers.S.inc"

movq x0, 0x1c80
mov  x3, x0
movq x1, 0xacabacab
ubfx	w2, w0, #2, #14
bfi	w0, w1, #0, #8
bfi	w3, w1, #8, #8

write_to_tube w30, x29
