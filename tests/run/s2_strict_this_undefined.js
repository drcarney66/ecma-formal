// S2 end to end: a strict function called without a base has this undefined.
// expect: normal: undefined
"use strict"; function f() { return this; } f()
