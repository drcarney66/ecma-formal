// args: --bundle
// expect: normal: undefined
// print: Hello, world!
// print: true
// JS_BUNDLE_MODULE:greeting.txt
Hello, world!
// JS_BUNDLE_MODULE_ENTRYPOINT:main.mjs
import text from "./greeting.txt" with { type: "text" };
import textAgain from "./greeting.txt" with { type: "text" };
print(text.trim());
print(typeof text === "string" && text === textAgain);
