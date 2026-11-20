// expect: normal: "get size|true"
// CreateIntrinsics step 2 (Erratum CreateIntrinsicsAsyncArgument): the
// test262 reading passes a getter its prefix and Array.fromAsync its [[Async]].
var r = [];
r.push(Object.getOwnPropertyDescriptor(Map.prototype, "size").get.name);
r.push(Array.fromAsync([1]) instanceof Promise);
r.join("|");
