// Reflect (§28.1) and the tables of %JSON%, %RegExp.prototype% and the
// iterator prototypes (JS/Builtins/Table.lean).
// expect: normal: "2,b,a|false|true|1|[object JSON]|[object Reflect]|true|[object Array Iterator]|true"
var o = { b: 1 }; o.a = 2; o[2] = 3;
Object.preventExtensions(o);
var r = [
  Reflect.ownKeys(o).join(),
  Reflect.defineProperty(o, "z", { value: 1 }),
  Reflect.has(o, "toString"),
  Reflect.apply(function () { return this.b; }, o, []),
  Object.prototype.toString.call(JSON),
  Object.prototype.toString.call(Reflect),
  RegExp.prototype.constructor === RegExp,
  Object.prototype.toString.call([][Symbol.iterator]()),
  // %Iterator.prototype%[Symbol.iterator] returns its this value
  Object.getPrototypeOf(Object.getPrototypeOf([][Symbol.iterator]()))[Symbol.iterator].call(Reflect) === Reflect
];
r.join("|")
