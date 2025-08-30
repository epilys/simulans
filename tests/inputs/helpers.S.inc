// load a 64-bit immediate using MOV
.macro movq Xn, imm
  movz    \Xn,  \imm & 0xFFFF
  movk    \Xn, (\imm >> 16) & 0xFFFF, lsl 16
  movk    \Xn, (\imm >> 32) & 0xFFFF, lsl 32
  movk    \Xn, (\imm >> 48) & 0xFFFF, lsl 48
.endm

// load a 32-bit immediate using MOV
.macro movl Wn, imm
  movz    \Wn,  \imm & 0xFFFF
  movk    \Wn, (\imm >> 16) & 0xFFFF, lsl 16
.endm

.macro write_to_tube Wm, Xn
  mov     \Wm, #1
  movz    \Xn,  0x0d800020 & 0xFFFF
  movk    \Xn, (0x0d800020 >> 16) & 0xFFFF, lsl 16
  movk    \Xn, (0x0d800020 >> 32) & 0xFFFF, lsl 32
  movk    \Xn, (0x0d800020 >> 48) & 0xFFFF, lsl 48
  strb \Wm, [\Xn]
.endm
