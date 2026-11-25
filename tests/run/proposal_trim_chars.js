// expect: normal: undefined
// print: ok

function assertEq(actual, expected, msg) {
  if (!Object.is(actual, expected)) {
    throw new Error((msg || "mismatch") + ": got " + String(actual) + ", expected " + String(expected));
  }
}

// Default whitespace trimming still works
assertEq("  \t\nhello\r\n ".trim(), "hello", "default trim");
assertEq("  hello  ".trimStart(), "hello  ", "default trimStart");
assertEq("  hello  ".trimEnd(), "  hello", "default trimEnd");
assertEq("  hello  ".trim(undefined), "hello", "explicit undefined");

// Specific character sets
assertEq("---hello---".trim("-"), "hello", "trim '-'");
assertEq("/_/_path/_/_".trim("/_"), "path", "trim multi-char set");
assertEq("/_/_path/_/_".trimStart("/_"), "path/_/_", "trimStart multi-char set");
assertEq("/_/_path/_/_".trimEnd("/_"), "/_/_path", "trimEnd multi-char set");
assertEq("abc".trim(""), "abc", "empty trimSet");
assertEq("aaaa".trim("a"), "", "all trimmed");

// Full Unicode code points (astral plane emoji U+1F600 = \uD83D\uDE00)
assertEq("\u{1F600}\u{1F600}hi\u{1F600}".trim("\u{1F600}"), "hi", "astral code point trim");
// Does not split surrogate pairs when trimming a different astral char with shared high surrogate (\uD83D\uDE01)
assertEq("\u{1F601}hi\u{1F601}".trim("\u{1F600}"), "\u{1F601}hi\u{1F601}", "distinct astral code point preserved");

// Non-String characters argument throws TypeError
for (const bad of [null, 123, true, {}, /a/]) {
  let threw = false;
  try {
    "abc".trim(bad);
  } catch (e) {
    threw = e instanceof TypeError;
  }
  assertEq(threw, true, "TypeError for non-string characters: " + String(bad));
}

print("ok");
