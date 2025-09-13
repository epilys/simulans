.include "tests/inputs/helpers.S.inc"

movq x0, 0x1c85
sbfx x1, x0, 2, 6
ubfx x2, x0, 2, 6
sbfx x3, x0, 2, 5
ubfx x4, x0, 2, 5

write_to_tube w30, x29
