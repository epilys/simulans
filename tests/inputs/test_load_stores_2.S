.macro write_to_tube Wm, Xn
  mov     \Wm, #1
  movz    \Xn,  0x0d800020 & 0xFFFF
  movk    \Xn, (0x0d800020 >> 16) & 0xFFFF, lsl 16
  movk    \Xn, (0x0d800020 >> 32) & 0xFFFF, lsl 32
  movk    \Xn, (0x0d800020 >> 48) & 0xFFFF, lsl 48
  strb \Wm, [\Xn]
.endm
mov x0, #0x1234
str x0, [sp, #-0x10]!
ldr x1, [sp], #0x10
add x0, x0, x1
write_to_tube w30, x29
