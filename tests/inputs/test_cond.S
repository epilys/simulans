.include "tests/inputs/helpers.S.inc"

// Set and Clear NZCV field macros, equivalent C code:
// ```c
// #include <stdint.h>
// 
// enum NZCVBit {
//   N = 31,
//   Z = 30,
//   C = 29,
//   V = 28,
// };
// 
// #define CLEAR(field)                                                           \
//   void clear##field(void) {                                                    \
//     uint64_t nzcv;                                                             \
//     __asm volatile("mrs %0, NZCV" : "=r"(nzcv)::);                             \
//     nzcv &= ~(1 << (field));                                                   \
//     __asm volatile("msr NZCV, %0" ::"r"(nzcv) :);                              \
//   }
// 
// #define SET(field)                                                             \
//   void set##field(void) {                                                      \
//     uint64_t nzcv;                                                             \
//     __asm volatile("mrs %0, NZCV" : "=r"(nzcv)::);                             \
//     nzcv |= 1 << (field);                                                      \
//     __asm volatile("msr NZCV, %0" ::"r"(nzcv) :);                              \
//   }
// 
// #define DEF(field)                                                             \
//   CLEAR(field);                                                                \
//   SET(field);
// 
// DEF(N);
// DEF(Z);
// DEF(C);
// DEF(V);
//```

.macro clearN 
  mrs     x30, NZCV
  and     x30, x30, #0x7fffffff
  msr     NZCV, x30
.endm

.macro setN
  mrs     x30, NZCV
  orr     x30, x30, #0xffffffff80000000
  msr     NZCV, x30
.endm

.macro clearZ
  mrs     x30, NZCV
  and     x30, x30, #0xffffffffbfffffff
  msr     NZCV, x30
.endm

.macro setZ
  mrs     x30, NZCV
  orr     x30, x30, #0x40000000
  msr     NZCV, x30
.endm

.macro clearC
  mrs     x30, NZCV
  and     x30, x30, #0xffffffffdfffffff
  msr     NZCV, x30
.endm

.macro setC
  mrs     x30, NZCV
  orr     x30, x30, #0x20000000
  msr     NZCV, x30
.endm

.macro clearV
  mrs     x30, NZCV
  and     x30, x30, #0xffffffffefffffff
  msr     NZCV, x30
.endm

.macro setV
  mrs     x30, NZCV
  orr     x30, x30, #0x10000000
  msr     NZCV, x30
.endm

// NZCV pseudo-register layout:
// - N, bit [31]
// - Z, bit [30]
// - C, bit [29]
// - V, bit [28]

clearN
clearZ
clearC
clearV

movq x0, 0xF0CACC1A
movq x1, 0xCAFEB0BA

setZ
csel x2, x0, x1, eq
csel x3, x0, x1, ne

clearZ
csel x4, x0, x1, eq
csel x5, x0, x1, ne

setC
csel x6, x0, x1, cs
csel x7, x0, x1, cc

clearC
csel x8, x0, x1, cs
csel x9, x0, x1, cc

setN
csel x10, x0, x1, mi
csel x11, x0, x1, pl

clearN
csel x12, x0, x1, mi
csel x13, x0, x1, pl

setV
csel x14, x0, x1, vs
csel x15, x0, x1, vc

clearV
csel x16, x0, x1, vs
csel x17, x0, x1, vc

setC
clearZ
csel x18, x0, x1, hi
csel x19, x0, x1, ls

setN
setV
csel x20, x0, x1, ge
csel x21, x0, x1, lt

clearV
csel x22, x0, x1, ge
csel x23, x0, x1, lt

clearZ
clearN
csel x24, x0, x1, gt
csel x25, x0, x1, le

setV
csel x26, x0, x1, gt
csel x27, x0, x1, le

csel x28, x0, x1, al
csel x29, x0, x1, nv

movq x30, 0x0d800020
mov sp, x30
mov x30, #1
strb w30, [sp]
