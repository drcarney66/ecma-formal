// expect: normal: "true,true,true,NaN"
let r = [];
try { eval("var x = ;"); } catch (e) { r.push(e instanceof SyntaxError); }
try { Function("a", "return a +;"); } catch (e) { r.push(e instanceof SyntaxError); }
try { new RegExp("("); } catch (e) { r.push(e instanceof SyntaxError); }
r.push(+"not-a-number");
r.join(",");
