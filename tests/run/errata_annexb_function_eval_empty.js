// args: --web-browser
// expect: normal: "undefined,42"
[String(eval("{ function f() { return 1; } }")), eval("42; { function g() {} }")].join(",");
