// expect: normal: "RangeError,0,RangeError,a"
let out = [];
try { "a".repeat(2 ** 30); out.push("ok"); } catch (e) { out.push(e.name); }
out.push("".repeat(2 ** 40).length);
try { "a".padStart(2 ** 30, "b"); out.push("ok"); } catch (e) { out.push(e.name); }
out.push("a".padStart(2 ** 32, ""));
out.join(",");
