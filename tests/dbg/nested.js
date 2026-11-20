function f() { throw 1; }
function g() { return f(); }
try { g(); } catch (e) {}
g();
