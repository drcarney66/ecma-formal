// S2 end to end: the unmapped arguments object of a strict function.
// expect: normal: 4
"use strict"; function f() { return arguments.length + arguments[1]; } f(1, 2)
