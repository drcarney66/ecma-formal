// The own-property table: the greatest array
// index 4294967294 and the first key past it (a String, after "length" in
// creation order), a sparse array, "01" (a String key, not an index), and a
// truncation that deletes the sparse indices.
// expect: normal: "0,7,4294967294,length,4294967295,01|4294967295|undefined|1"
var a = [];
a[4294967294] = 'max';
a[4294967295] = 'past';
a[7] = 'seven';
a["01"] = 'zero-one';
a[0] = 'zero';
var r = Object.getOwnPropertyNames(a).join();
var len = a.length;
a.length = 3;
r + '|' + len + '|' + a[4294967294] + '|' + Object.keys(a).filter(function (k) { return k !== "01" && k !== "4294967295"; }).length
