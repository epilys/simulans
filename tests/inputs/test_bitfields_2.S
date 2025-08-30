.include "tests/inputs/helpers.S.inc"

movq x0, 0x1c80
ubfx	w2, w0, #2, #14

write_to_tube w30, x29
