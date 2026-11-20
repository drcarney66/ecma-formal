async function h() {
  throw 1;
}
function g() {
  h();
  return 2;
}
function f() {
  try { throw 3; } catch {}
}
function k() {
  return f();
}
var r = g();
k();
r = r + 1;
// A throw the spec consumes without a catch statement in the caller (an async function's
// rejection, an empty catch in the callee): next and stepOut after it land in the caller at
// the call, as a return does.
