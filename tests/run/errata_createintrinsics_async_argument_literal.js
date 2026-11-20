// expect: stop: erratum CreateIntrinsicsAsyncArgument sec-setfunctionname#0 5.a
// args: --erratum CreateIntrinsicsAsyncArgument=literal
// CreateIntrinsics step 2 (Erratum CreateIntrinsicsAsyncArgument): the literal
// reading passes [[Async]] as CreateBuiltinFunction's prefix, SetFunctionName
// concatenates a Boolean, and realm creation stops as the erratum.
var r = [];
r.push(Object.getOwnPropertyDescriptor(Map.prototype, "size").get.name);
r.push(Array.fromAsync([1]) instanceof Promise);
r.join("|");
