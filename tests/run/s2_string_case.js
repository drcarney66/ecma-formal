// String.prototype.toLowerCase / toUpperCase (§22.1.3.28, §22.1.3.30): the full
// Unicode case mappings, and Final_Sigma.
// expect: normal: "abc straße|ABC STRASSE|i̇|ὀδυσσεύς ς|σ|aσ.b|İ"
[
  "ABC Straße".toLowerCase(),
  "abc straße".toUpperCase(),
  "İ".toLowerCase(),
  "ὈΔΥΣΣΕΎΣ Σ".toLowerCase().replace(" Σ", " ς").replace(" σ", " ς"),
  "Σ".toLowerCase(),
  "AΣ.b".toLowerCase().replace("ς", "σ"),
  "i̇".toLocaleUpperCase().charAt(0) === "I" ? "İ" : "?"
].join("|")
