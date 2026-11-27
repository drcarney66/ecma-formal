// expect: normal: "a,1,null,0,,1"
const r = /a/g;
const m1 = r.exec("a")[0];
const i1 = r.lastIndex;
const m2 = String(r.exec("a"));
const i2 = r.lastIndex;
const m3 = /(?:)/u.exec("")[0];
const m4 = /$/gu.exec("x").index;
[m1, i1, m2, i2, m3, m4].join(",");
