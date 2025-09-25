.include "tests/inputs/helpers.S.inc"

crc32b w2, w0, w1
crc32h w3, w0, w1
crc32w w4, w0, w1
crc32x w5, w0, x1

write_to_tube w30, x29
