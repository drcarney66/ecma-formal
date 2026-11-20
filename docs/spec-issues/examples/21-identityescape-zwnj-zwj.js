// IdentityEscape[~UnicodeMode] :: SourceCharacter but not UnicodeIDContinue
// (§22.2.1). Since Unicode 15.1, U+200C (ZWNJ) and U+200D (ZWJ) are
// ID_Continue, so the literal text rejects `\` followed by either of them in
// a pattern without the u or v flag; before Unicode 15.1 it accepted them.
// U+200B and U+200E (not ID_Continue) are the neighbours; `a` (U+0061,
// ID_Continue) is an IdentityEscape only in §B.1.2's grammar, which every
// engine implements. The pattern text is built with fromCharCode: the
// characters are invisible.
if (typeof print === "undefined") globalThis.print = console.log;
for (var cu of [0x200C, 0x200D, 0x200B, 0x200E, 0x61]) {
  var ch = String.fromCharCode(cu), src = "\\" + ch, out = [];
  try { var re = eval("/" + src + "/"); out.push("literal " + (re.source === src && re.test(ch))); }
  catch (e) { out.push("literal " + e.constructor.name); }
  try { out.push("RegExp " + new RegExp(src).test(ch)); }
  catch (e) { out.push("RegExp " + e.constructor.name); }
  try { new RegExp(src, "u"); out.push("u ok"); }
  catch (e) { out.push("u " + e.constructor.name); }
  print("U+" + cu.toString(16).toUpperCase() + ": " + out.join(", "));
}
