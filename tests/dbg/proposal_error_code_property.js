const err = new Error("connect failed", { code: "ECONNREFUSED", cause: "timeout" });
const sup = new SuppressedError(err, new TypeError("close failed"), "disposal failed", { code: "EDISPOSE" });
const desc = Object.getOwnPropertyDescriptor(err, "code");
print([
  "code=" + err.code,
  "enumerable=" + desc.enumerable,
  "suppressedCode=" + sup.code
].join(", "));
