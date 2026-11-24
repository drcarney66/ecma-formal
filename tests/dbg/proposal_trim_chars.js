const path = "/__ecma-262__/".trim("/_");
// U+1F601 (\uD83D\uDE01) shares high surrogate \uD83D with U+1F600 (\uD83D\uDE00)
const astral = "\u{1F601}ok\u{1F601}".trim("\u{1F600}");
print("path=" + path + ", astralPreserved=" + (astral === "\u{1F601}ok\u{1F601}"));
