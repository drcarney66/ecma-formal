// test262's $262.createRealm (INTERPRETING.md): InitializeHostDefinedRealm (§9.6) at run time, its
// execution context then removed, the caller's running again; it returns the new realm's $262, made by
// the same HostGlobalProperties step. The new realm has its own intrinsics and global object; the
// well-known symbols and Symbol.for's GlobalSymbolRegistry are the agent's, and an object a
// constructor of the new realm makes without a prototype object gets that realm's.
// expect: normal: "function,createRealm,0 ; true,false,false,true ; true,true ; true,true,true ; true,true ; true,true"
var f = $262.createRealm;
var r1 = [typeof f, f.name, f.length].join();
var o = f();
var g = o.global;
var r2 = [g.$262 === o, g === this, g.Array === Array, o.global.Object.getPrototypeOf(g) === g.Object.prototype].join();
var r3 = [Object.getPrototypeOf({}) === Object.prototype, [] instanceof Array].join();
var r4 = [g.Symbol.iterator === Symbol.iterator, g.Symbol.for("k") === Symbol.for("k"),
  Object.getPrototypeOf(o.createRealm) === g.Function.prototype].join();
var C = new g.Function();
C.prototype = null;
var a = Reflect.construct(Array, [], C);
var r5 = [Object.getPrototypeOf(a) === g.Array.prototype, Array.isArray(a)].join();
var o2 = o.createRealm();
var r6 = [o2.global !== g && o2.global !== this, g.eval("[] instanceof Array")].join();
[r1, r2, r3, r4, r5, r6].join(" ; ")
