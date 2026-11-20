// Proxy exotic objects (§10.5): every trap is called with the target, and a
// missing trap forwards to the target. Reflect.set with the Proxy as receiver
// defines the property through the Proxy (OrdinarySetWithOwnDescriptor, §10.1.9.2).
// expect: normal: "get:a,has:a,set:b,getOwnPropertyDescriptor:b,defineProperty:b,delete:b,ownKeys,getOwnPropertyDescriptor:a,defineProperty:c,getPrototypeOf,setPrototypeOf,isExtensible,preventExtensions|1|true|2|a,c|true"
var log = [];
var target = { a: 1 };
var handler = {
  get: function (t, k, r) { log.push("get:" + String(k)); return Reflect.get(t, k, r); },
  has: function (t, k) { log.push("has:" + String(k)); return k in t; },
  set: function (t, k, v, r) { log.push("set:" + String(k)); return Reflect.set(t, k, v, r); },
  deleteProperty: function (t, k) { log.push("delete:" + String(k)); return delete t[k]; },
  ownKeys: function (t) { log.push("ownKeys"); return Reflect.ownKeys(t); },
  getOwnPropertyDescriptor: function (t, k) {
    log.push("getOwnPropertyDescriptor:" + String(k));
    return Object.getOwnPropertyDescriptor(t, k);
  },
  defineProperty: function (t, k, d) { log.push("defineProperty:" + String(k)); return Reflect.defineProperty(t, k, d); },
  getPrototypeOf: function (t) { log.push("getPrototypeOf"); return Object.getPrototypeOf(t); },
  setPrototypeOf: function (t, p) { log.push("setPrototypeOf"); return Reflect.setPrototypeOf(t, p); },
  isExtensible: function (t) { log.push("isExtensible"); return Object.isExtensible(t); },
  preventExtensions: function (t) { log.push("preventExtensions"); return Reflect.preventExtensions(t); }
};
var p = new Proxy(target, handler);
var a = p.a;
var has = "a" in p;
p.b = 2;
var b = target.b;
delete p.b;
Reflect.ownKeys(p);
Object.getOwnPropertyDescriptor(p, "a");
Object.defineProperty(p, "c", { value: 3, configurable: true, enumerable: true });
Object.getPrototypeOf(p);
Object.setPrototypeOf(p, Object.prototype);
Object.isExtensible(p);
Object.preventExtensions(p);
log.join(",") + "|" + a + "|" + has + "|" + b + "|" + Object.keys(target).join(",") + "|" +
  (Object.isExtensible(target) === false)
