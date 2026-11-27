// args: --web-browser
// expect: normal: "a,a"
[/(?=a)+a/.exec("a")[0], /(?!b)*a/.exec("a")[0]].join(",");
