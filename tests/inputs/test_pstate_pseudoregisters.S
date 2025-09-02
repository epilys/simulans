.include "tests/inputs/helpers.S.inc"

  mrs x0, CurrentEL
quit:
  write_to_tube w30, x29
