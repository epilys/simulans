.include "tests/inputs/helpers.S.inc"

cmeq v0.8b, v0.8b, 0
cmeq v1.8b, v1.8b, v1.8b
cmgt v2.8b, v2.8b, 0
cmgt v3.8b, v3.8b, 0
cmgt v4.8b, v4.8b, 0
cmgt v5.2d, v5.2d, 0
cmgt v6.2d, v6.2d, 0

write_to_tube w30, x29
