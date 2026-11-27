// expect: normal: "true,true,a"
[
  /\uD800\uDC00+/u.test("\u{10000}\u{10000}"),
  /[\uD800\uDC00]/u.test("\u{10000}"),
  /(?<\uD835\uDC9C>a)/.exec("a").groups["\u{1D49C}"],
].join(",");
