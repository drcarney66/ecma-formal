// test262's host object (INTERPRETING.md), made by HostGlobalProperties (§9.6 step 17): $262.global is
// the global object; $262.detachArrayBuffer performs DetachArrayBuffer (§25.1.3.5), and throws a TypeError
// for an object that is no ArrayBuffer and for a SharedArrayBuffer.
// expect: normal: "true,function,detachArrayBuffer,1 ; true,0 ; TypeError,TypeError ; true,false ; true"
var ab = new ArrayBuffer(8);
var f = $262.detachArrayBuffer;
var r = [$262.global === this, typeof f, f.name, f.length].join();
f(ab);
var r2 = [ab.detached, ab.byteLength].join();
var e = [];
try { f({}); } catch (x) { e.push(x.constructor.name); }
try { f(new SharedArrayBuffer(1)); } catch (x) { e.push(x.constructor.name); }
var d = Object.getOwnPropertyDescriptor(this, "$262");
var p = Object.getOwnPropertyDescriptor(this, "print");
[r, r2, e.join(), [d.writable && d.configurable, d.enumerable].join(), p.enumerable].join(" ; ")
