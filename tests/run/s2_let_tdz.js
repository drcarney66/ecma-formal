// S2 end to end: reading a let binding before its declaration throws a ReferenceError.
// expect: normal: "ReferenceError"
try { t; let t = 1; } catch (e) { e.name }
