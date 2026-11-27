// args: --checked
// expect: normal: "true,5,true,9"
const t = { x: 1 };
const p = new Proxy(t, { getOwnPropertyDescriptor() { return undefined; } });
const ok1 = Reflect.set({}, "x", 5, p);
const proto = { y: 2 };
const child = Object.create(proto);
const ok2 = Reflect.set({}, "y", 9, child);
[ok1, t.x, ok2, child.y].join(",");
