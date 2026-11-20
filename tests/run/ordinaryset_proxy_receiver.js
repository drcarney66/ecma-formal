// expect: normal: undefined
// print: true
// print: 5
// OrdinarySetWithOwnDescriptor 2.d.i asserts that the receiver "does not
// currently have a property" P after its [[GetOwnProperty]] returned
// undefined. A Proxy receiver's trap may hide a property its target has: the
// target t has x, the trap answers undefined, and CreateDataProperty then
// redefines t.x through the Proxy. The model reads the Assert as unchecked
// (an editorial report, docs/spec-issues/38); a reading
// that looks through the Proxy makes it fail.
var t = { x: 1 };
var p = new Proxy(t, { getOwnPropertyDescriptor() { return undefined; } });
print(Reflect.set({}, "x", 5, p));
print(t.x);
