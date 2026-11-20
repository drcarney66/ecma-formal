// FinalizationRegistry.prototype.unregister step 5 removes cells from the List its For each iterates.
if (typeof print === "undefined") globalThis.print = console.log;
var fr = new FinalizationRegistry(function () {});
var token = {}, t1 = {}, t2 = {}, t3 = {};
fr.register(t1, 1, token);
fr.register(t2, 2, token);
fr.register(t3, 3, {});
print(fr.unregister(token));
print(fr.unregister(token));
