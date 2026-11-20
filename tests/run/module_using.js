// module: yes
// expect: normal: undefined
// print: body
// print: disposed
// A `using` declaration at the top level of a Module is disposed when the
// module body completes (ExecuteModule step 3.f, §16.2.1.7.3.2).
using r = { [Symbol.dispose]() { print("disposed"); } };
print("body");
