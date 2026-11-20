if (typeof print === "undefined") globalThis.print = console.log;
await using a = { async [Symbol.asyncDispose]() { print("dispose a"); } };
using b = { [Symbol.dispose]() { print("dispose b"); } };
await null;
print("end of module body");
