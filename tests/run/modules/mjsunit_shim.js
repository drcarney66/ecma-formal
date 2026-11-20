// The mjsunit assertions V8's d8 tests call, as a Script prelude: a failed one throws an Error.
function mjsunitDeepEquals(a, b) {
  if (Object.is(a, b)) return true;
  if (typeof a !== "object" || typeof b !== "object" || a === null || b === null) return false;
  if (Object.getPrototypeOf(a) !== Object.getPrototypeOf(b)) return false;
  var ka = Object.keys(a), kb = Object.keys(b);
  if (ka.length !== kb.length) return false;
  for (var i = 0; i < ka.length; i++) {
    if (!Object.prototype.hasOwnProperty.call(b, ka[i]) || !mjsunitDeepEquals(a[ka[i]], b[ka[i]])) return false;
  }
  return true;
}
function mjsunitFail(what, msg) {
  throw new Error(what + (msg === undefined ? "" : ": " + msg));
}
function assertEquals(expected, found, msg) {
  if (!mjsunitDeepEquals(expected, found)) mjsunitFail("assertEquals " + String(expected) + " " + String(found), msg);
}
function assertNotEquals(expected, found, msg) {
  if (mjsunitDeepEquals(expected, found)) mjsunitFail("assertNotEquals " + String(expected), msg);
}
function assertTrue(value, msg) { assertEquals(true, value, msg); }
function assertFalse(value, msg) { assertEquals(false, value, msg); }
function assertUnreachable(msg) { mjsunitFail("assertUnreachable", msg); }
function assertThrows(code, type, msg) {
  try { code(); } catch (e) {
    if (type !== undefined && !(e instanceof type)) mjsunitFail("assertThrows: wrong exception " + String(e), msg);
    return e;
  }
  mjsunitFail("assertThrows: did not throw", msg);
}
function assertPromiseResult(promise, success, fail) {
  return promise.then(success === undefined ? function () {} : success,
    fail === undefined ? function (e) { mjsunitFail("assertPromiseResult: rejected " + String(e)); } : fail);
}
