// CreateIntrinsics step 2 passes _async_ where CreateBuiltinFunction takes _prefix_, and passes no _prefix_.
if (typeof print === "undefined") globalThis.print = console.log;
print(Object.getOwnPropertyDescriptor(Map.prototype, "size").get.name);
print(Object.getOwnPropertyDescriptor(RegExp.prototype, "flags").get.name);
var p = Array.fromAsync([1, 2]);
print(Object.prototype.toString.call(p));
p.then(function (v) { print("fromAsync fulfils with " + JSON.stringify(v)); });
