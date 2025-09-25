.include "tests/inputs/helpers.S.inc"

// This test must be run after enabling the MMU

// Cause abort with translation fault by writing to unmapped address
movq x0, 0xacab
str x1, [x0]

write_to_tube w30, x29
