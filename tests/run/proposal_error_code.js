// expect: normal: undefined
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

// Error, NativeErrors, AggregateError, SuppressedError all install non-enumerable `code`
const e1 = new Error("boom", { code: "ERR_BOOM", cause: 42 });
assertEq(e1.code, "ERR_BOOM", "Error code");
assertEq(e1.cause, 42, "Error cause");
const d1 = Object.getOwnPropertyDescriptor(e1, "code");
assertEq(d1.writable, true, "writable");
assertEq(d1.enumerable, false, "enumerable");
assertEq(d1.configurable, true, "configurable");

// Value is stored as-is (no ToString coercion in InstallErrorOwnProperties)
const sym = Symbol("err");
const te = new TypeError("bad", { code: sym });
assertEq(te.code, sym, "TypeError symbol code");

const ae = new AggregateError([1, 2], "agg", { code: 404, cause: "root" });
assertEq(ae.code, 404, "AggregateError code");
assertEq(ae.cause, "root", "AggregateError cause");

const se = new SuppressedError(new Error("e"), new Error("s"), "sup", { code: "E_SUP", cause: "c0" });
assertEq(se.code, "E_SUP", "SuppressedError code");
assertEq(se.cause, "c0", "SuppressedError cause");

// Absent vs present-undefined `code`
const noCode = new Error("plain", {});
assertEq("code" in noCode, false, "absent code not installed");
const undefCode = new Error("undef", { code: undefined });
assertEq("code" in undefCode, true, "present undefined code installed");
assertEq(undefCode.code, undefined, "present undefined code value");

// Observable order: HasProperty/Get("cause") before HasProperty/Get("code")
const log = [];
const opts = new Proxy({ cause: "c", code: "k" }, {
  has(t, p) { log.push("has:" + String(p)); return p in t; },
  get(t, p, r) { log.push("get:" + String(p)); return Reflect.get(t, p, r); }
});
new RangeError("msg", opts);
assertEq(log.join(","), "has:cause,get:cause,has:code,get:code", "evaluation order");

print("ok");
