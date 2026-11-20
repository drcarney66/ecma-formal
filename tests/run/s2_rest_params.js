// S2 end to end: a rest parameter collects the remaining arguments into an Array.
// expect: normal: 5
function f(a, ...r) { return r.length + r[1]; } f(1, 2, 3)
