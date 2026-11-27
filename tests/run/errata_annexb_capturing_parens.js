// args: --checked --web-browser
// expect: normal: "true,a"
[/a+/.test("aa"), /(a)+/.exec("aa")[1]].join(",");
