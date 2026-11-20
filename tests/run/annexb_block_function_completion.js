// On a web-browser host, a block FunctionDeclaration's Evaluation (§B.3.2.2,
// §B.3.2.3) still has an empty completion value: the script's and eval's
// values are those of the statements before it. Its steps' abrupt completion
// (a global setter's throw) is the Evaluation's.
// args: --web-browser
// expect: normal: 2
// print: 1
// print: boom
print(eval("1; { function f(){} }"));
Object.defineProperty(globalThis, "h", { get() {}, set(v) { throw "boom"; }, configurable: true });
try { eval("{ function h(){} }"); print("no throw"); } catch (e) { print(e); }
2; { function g(){} }
