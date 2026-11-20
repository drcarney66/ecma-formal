if (typeof print === "undefined") globalThis.print = console.log;
print("c throws");
throw "c-error";
