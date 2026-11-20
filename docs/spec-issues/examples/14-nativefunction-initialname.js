// Function.prototype.toString step 3: for a built-in function whose
// [[InitialName]] no PropertyName matches, no String has "the syntax of a
// NativeFunction" with that name as its PropertyName portion. A class's
// default constructor is a built-in function (ClassDefinitionEvaluation
// 14.b) named by NamedEvaluation; on a host whose HostHasSourceTextAvailable
// is false, step 3 applies to it.
if (typeof print === "undefined") globalThis.print = console.log;
var o = { ["a b"]: class {} };
print(JSON.stringify(o["a b"].name));
class C { static #x = class {}; static name2() { return C.#x.name; } }
print(JSON.stringify(C.name2()));
var s = { [Symbol("a b")]: class {} };
print(JSON.stringify(s[Object.getOwnPropertySymbols(s)[0]].name));
// With source text available (every engine), step 2 returns the class text:
print(Function.prototype.toString.call(o["a b"]));
