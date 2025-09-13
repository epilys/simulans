.include "tests/inputs/helpers.S.inc"

sub sp, sp, #0x10
str w0, [sp, #8]
ldr w8, [sp, #8]
mov w9, #2
sdiv w8, w8, w9
sdiv w10, w8, wzr
mov w11, w8
neg w11, w11
sdiv w12, w8, w11
ldr w13, [sp, #8]
add w13, w13, w13
udiv w14, w13, w0

write_to_tube w30, x29
