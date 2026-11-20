// S2 end to end: a TypeError from the interpreter is caught and is an instance of %TypeError%.
// expect: normal: true
try { null.x; } catch (e) { e instanceof TypeError }
