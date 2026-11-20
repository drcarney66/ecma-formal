// BuiltinCallOrConstruct 10.b.iii and AsyncBlockStart 1.f: the fulfilment
// value of a built-in async function. Literal text: undefined.
if (typeof print === "undefined") globalThis.print = console.log;
Array.fromAsync([1, 2]).then(function (v) {
  print("fromAsync fulfils with " + JSON.stringify(v));
});
