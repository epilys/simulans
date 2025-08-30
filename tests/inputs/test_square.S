.include "tests/inputs/helpers.S.inc"

bl #8
b #0x24
sub sp, sp, #0x10
str w0, [sp, #0xc]
ldr w8, [sp, #0xc]
ldr w9, [sp, #0xc]
mul w0, w8, w9
add sp, sp, #0x10
nop
write_to_tube w30, x29
