// OrdinarySetWithOwnDescriptor 2.d.i asserts that the receiver "does not currently have" the property right
// after a Proxy receiver's trap said undefined for a property its target has.
if (typeof print === "undefined") globalThis.print = console.log;
var t = { x: 1 };
var p = new Proxy(t, { getOwnPropertyDescriptor() { return undefined; } });
print(Reflect.set({}, "x", 5, p));
print(t.x);
