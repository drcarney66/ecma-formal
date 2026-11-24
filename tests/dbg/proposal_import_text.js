// JS_BUNDLE_MODULE:greeting.txt
Hello from ECMA-262 Import Text!
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import greeting from "./greeting.txt" with { type: "text" };
const dyn = await import("./greeting.txt", { with: { type: "text" } });
print(greeting.trim() + " | cached=" + (greeting === dyn.default));
