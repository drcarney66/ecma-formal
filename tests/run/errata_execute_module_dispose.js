// module: yes
// expect: normal: undefined
// print: end
// print: disposed
// A module with top-level await and `await using` (Erratum ExecuteModuleAsyncDisposeResources):
// the test262 reading disposes the module's resources after its body.
await using x = { [Symbol.asyncDispose]() { print("disposed"); } };
await 0;
print("end");
