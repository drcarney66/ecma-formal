// module: yes
// expect: normal: undefined
// print: end
// args: --erratum ExecuteModuleAsyncDisposeResources=literal
// A module with top-level await and `await using` (Erratum ExecuteModuleAsyncDisposeResources):
// the literal ExecuteModule step 4.b never disposes the module's resources.
await using x = { [Symbol.asyncDispose]() { print("disposed"); } };
await 0;
print("end");
