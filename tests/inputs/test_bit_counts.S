.include "tests/inputs/helpers.S.inc"

movq x0, 0b00000000000000000000000000000000
movq x1, 0b00000000000000001000000000000000

clz x2, x0
clz x3, x1

clz w4, w0
clz w5, w1

// movq x6, 0b11000000000000000000000000000000

// [ref:cranelift_ice]: Compilation(Unsupported("should be implemented in ISLE: inst = `v189 = cls.i64 v187`, type = `Some(types::I64)`"))
// cls x7, x6
// [ref:cranelift_ice]
// cls w8, w6

// [ref:FEAT_CSSC]
// cnt x9, x6
// cnt w10, w6
// cnt w11, w1

write_to_tube w30, x29
