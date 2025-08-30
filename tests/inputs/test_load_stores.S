.include "tests/inputs/helpers.S.inc"

str x0, [sp, #-0x10]!
ldr x1, [sp], #0x10
write_to_tube w30, x29
