.include "tests/inputs/helpers.S.inc"

adr x30, halt
// 0x400814e4 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE>
cbz     x2, _write_str_ret // 0x40081524 // <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h
// 0x400814e8 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+4>
adr x1, literal
// 0x400814ec <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+8>
add     x9, x1, x2
// 0x400814f0 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+12>
ldrb    w10, [x1], #1
// 0x400814f4 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+16>
ldrh    w11, [x0, #26]
// 0x400814f8 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+20>
tbnz    w11, #5, _write_str_isb // 0x40081514 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_s
// 0x400814fc <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+24>
_write_str_cmp:
cmp     x1, x9
// 0x40081500 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+28>
strh    w10, [x0]
// 0x40081504 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+32>
b.eq    _write_str_ret //0x40081524 // <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe5
// 0x40081508 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+36>
ldrb    w10, [x1], #1
// 0x4008150c <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+40>
ldrh    w11, [x0, #26]
// 0x40081510 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+44>
tbz     w11, #5, _write_str_cmp // 0x400814fc <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_s
// 0x40081514 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+48>
_write_str_isb:
isb
// 0x40081518 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+52>
ldrh    w11, [x0, #26]
// 0x4008151c <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+56>
tbnz    w11, #5, _write_str_isb // 0x40081514 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_s
// 0x40081520 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+60>
b       _write_str_cmp // == 0x400814fc // <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe5
// 0x40081524 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+64>
_write_str_ret:
mov     w0, wzr
// 0x40081528 <_ZN53_$LT$pl011_uart..Uart$u20$as$u20$core..fmt..Write$GT$9write_str17h4fe56bcb77973a8eE+68>
ret
literal:
   .ascii "Hello world\n"
halt:
  write_to_tube w30, x29
