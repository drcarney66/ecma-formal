// String.prototype.toLocaleUpperCase / toLocaleLowerCase (§22.1.3.26–27), localeCompare
// (§22.1.3.12) and Number / BigInt toLocaleString (§21.1.3.4, §21.2.3.2) on a host without
// ECMA-402 whose locale has no rules of its own: the forms without a locale.
// expect: normal: "ABC STRASSE|abc straße|i̇|-1,1,0,0|TypeError|7,-1.5,12"
[
  "abc straße".toLocaleUpperCase(),
  "ABC Straße".toLocaleLowerCase(),
  "İ".toLocaleLowerCase(),
  [Math.sign("a".localeCompare("b")), Math.sign("b".localeCompare("a")),
    "ab".localeCompare("ab"), "Å".localeCompare("Å")].join(),
  (function () {
    try { String.prototype.toLocaleUpperCase.call(null); } catch (e) { return e.constructor.name; }
  })(),
  [(7).toLocaleString(), (-1.5).toLocaleString(), 12n.toLocaleString()].join()
].join("|")
