function f() {
  throw 7;
}
var r;
try {
  f();
} catch (e) {
  r = e;
}
try { f(); } catch (e) { r = r + e; }
