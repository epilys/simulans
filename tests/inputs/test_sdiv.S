.include "tests/inputs/helpers.S.inc"

sub sp, sp, #0x10
str w0, [sp, #8]
ldr w8, [sp, #8]
mov w9, #2
sdiv w8, w8, w9

write_to_tube w30, x29
