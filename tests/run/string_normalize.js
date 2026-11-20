// String.prototype.normalize (§22.1.3.15) in the four forms, and
// localeCompare (§22.1.3.12), which honours canonical equivalence.
// expect: normal: "1E69,73 323 307,1E9B 323,17F 323 307|0"
var s = "ẛ̣";
var hex = function (t) {
  var out = [];
  for (var i = 0; i < t.length; i++) out.push(t.charCodeAt(i).toString(16).toUpperCase());
  return out.join(" ");
};
[hex(s.normalize("NFKC")), hex(s.normalize("NFKD")), hex(s.normalize()), hex(s.normalize("NFD"))].join()
  + "|" + "ḍ̇".localeCompare("ḍ̇")
