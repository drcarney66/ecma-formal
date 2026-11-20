// String methods of §22.1.3: trim*, pad*, repeat, split, replace/replaceAll with
// GetSubstitution patterns, fromCodePoint, raw and well-formedness.
// expect: normal: "a b|x |[ x]|xyxab|ab  |ababab|a,b,,c|a,b|a[X|a|bXc]bXc|a0b2c|2|a1b2c|65533,false"
var r = [];
r.push(" \t a b  ".trim());
r.push(" x ".trimStart());
r.push("[" + " x ".trimEnd() + "]");
r.push("ab".padStart(5, "xy"));
r.push("ab".padEnd(4));
r.push("ab".repeat(3) + "".repeat(2147483647));
r.push("a,b,,c".split(",").join());
r.push("a,b,c".split(",", 2).join());
r.push("aXbXc".replace("X", "[$&|$`|$']"));
r.push("aXbXc".replaceAll("X", function (m, p) { return p - 1; }));
r.push(String.fromCodePoint(0x1F600).length);
r.push(String.raw({ raw: ["a", "b", "c"] }, 1, 2));
r.push("a\uD800b".toWellFormed().charCodeAt(1) + "," + "a\uD800".isWellFormed());
r.join("|")
