// S2 end to end: a sloppy function with a non-simple parameter list gets an unmapped arguments object.
// expect: normal: 7
function f(a = 1) { return a + arguments.length; } f() + f(5)
