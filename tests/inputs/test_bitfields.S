.include "tests/inputs/helpers.S.inc"

movq x1, 0x55555555
movq x2, 0xaaaaaaaa
ubfiz   x3, x1, 5, 3
ubfiz   x4, x1, 0, 5
ubfiz   x5, x1, 63, 1
bfc x2, #3, #5

write_to_tube w30, x29
