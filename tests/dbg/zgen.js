function* g() { yield 1; }
var it = g();
it.next();
try { it.throw(5); } catch (e) {}
