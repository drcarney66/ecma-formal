// String.prototype.split step 10.d passes a List of code units to CreateArrayFromList, which takes a List
// of ECMAScript language values.
if (typeof print === "undefined") globalThis.print = console.log;
var a = "ab".split("");
print(a.length + " " + typeof a[1] + " " + JSON.stringify(a));
print(new String(" ").split("")[0] === " ");
print(JSON.stringify("\u{1F600}".split("")));
