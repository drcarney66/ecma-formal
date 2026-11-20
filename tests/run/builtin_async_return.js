// expect: normal: undefined
// print: undefined
// print: 1,2
// BuiltinCallOrConstruct step 10.b.iii under Erratum BuiltinReturnCompletion
// (its test262 reading): "Return array" of Array.fromAsync is a normal
// completion, which the resultsClosure gives to AsyncBlockStart as a return
// completion, so the promise is fulfilled with the array; disposeAsync's
// "Return ? DisposeResources(…)" fulfils it with undefined.
Array.fromAsync([1, 2]).then(function (a) { print(a.join(",")); });
new AsyncDisposableStack().disposeAsync().then(function (v) { print(String(v)); });
void 0;
