# 32. Identifier early errors take the StringValue of a |ReservedWord|, which StringValue does not define

- **Location:** §13.1.1 Static Semantics: Early Errors (`#sec-identifiers-static-semantics-early-errors`), the last
  rule for `Identifier : IdentifierName but not ReservedWord`, with §13.1.2 Static Semantics: StringValue
  (`#sec-static-semantics-stringvalue`) and §12.7.2 Keywords and Reserved Words (`#sec-keywords-and-reserved-words`).
- **Kind:** missing case (a syntax-directed operation applied to a nonterminal it has no rows for).
- **Model erratum:** `StringValueReservedWord`, default reading test262; its readings: literal, test262, proposed.
  Read literally, the run stops at the rule (StringValue has no row); the test262 and proposed readings compare with
  the String value of the code points of each terminal of |ReservedWord| other than `yield` and `await`.
- **Upstream:** Checked 2026-11-19: issue #1865 (open, 2020-02), ""StringValue of ReservedWord" is used but not
  defined", reports it; a reply there (2020-02-05) answers that "A reserved word is an IdentifierName", so that
  StringValue's |IdentifierName| row is meant to apply. No pull request was found.

## Text

The rule:

> It is a Syntax Error if the StringValue of |IdentifierName| is the StringValue of any |ReservedWord| except for
> `yield` or `await`.

StringValue's rows are for |IdentifierName|, `IdentifierReference`/`BindingIdentifier`/`LabelIdentifier` :
`yield` and `await`, `Identifier : IdentifierName but not ReservedWord`, |PrivateIdentifier| and
`ModuleExportName : StringLiteral`. |ReservedWord| is

> ReservedWord :: one of `await` `break` `case` … `yield`

and §12.7.2 says "A reserved word is an |IdentifierName| that cannot be used as an identifier."

## Problem

StringValue is a syntax-directed operation: it is defined on the Parse Nodes of the productions it has rows for.
The rule applies it to "any |ReservedWord|", which is neither a Parse Node at the rule's site (the node is
|Identifier|, whose only child is an |IdentifierName|) nor a nonterminal with a StringValue row. One might read
"reserved word" as the defined term of §12.7.2, an |IdentifierName|, so that StringValue's |IdentifierName| row
applies; but the rule names the nonterminal |ReservedWord|, whose productions have a single terminal each
(``ReservedWord :: `if` ``), and a
`ReservedWord` Parse Node is not an |IdentifierName| Parse Node, so the |IdentifierName| row does not reach it.

The intended meaning is clear from the note after the rule ("such escapes cannot be used to write an |Identifier|
whose code point sequence is the same as a |ReservedWord|") and from test262: the comparison is with the String
value of each reserved word's code points. The fix states that directly. (§12.7.2's note, "rule out identifiers
with the same StringValue as a reserved word", is informal and can stay.)

## Examples

[examples/32-stringvalue-reservedword.js](examples/32-stringvalue-reservedword.js) (outputs:
[RESULTS.md](examples/RESULTS.md#32-stringvalue-reservedwordjs)), each source parsed as a Script:

```js
var sources = ["var \\u0069f = 1;", "var i\\u0066 = 1;", "var \\u{63}lass = 1;", "var \\u0079ield = 1;",
               "var \\u0061wait = 1;", "var \\u0069g = 1;"];
for (var s of sources) {
  try { (0, eval)(s); print(s + ": no error"); }
  catch (e) { print(s + ": " + e.constructor.name); }
}
```

| | `\u0069f` | `i\u0066` | `\u{63}lass` | `\u0079ield` | `\u0061wait` | `\u0069g` |
|---|---|---|---|---|---|---|
| literal text | — | — | — | — | — | — |
| V8, SpiderMonkey, JavaScriptCore | SyntaxError | SyntaxError | SyntaxError | no error | no error | no error |
| formal model, test262 and proposed readings | SyntaxError | SyntaxError | SyntaxError | no error | no error | no error |

"—": the rule is undefined for every name; the model's literal reading stops at the first source. The engines and
the model's other readings agree; the defect is in the text only.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -18406,7 +18406,7 @@
           It is a Syntax Error if the goal symbol of the syntactic grammar is |Module| and the StringValue of |IdentifierName| is *"await"*.
         </li>
         <li>
-          It is a Syntax Error if the StringValue of |IdentifierName| is the StringValue of any |ReservedWord| except for `yield` or `await`.
+          It is a Syntax Error if the StringValue of |IdentifierName| is the String value of the code points of a terminal symbol of |ReservedWord| other than `yield` and `await`.
         </li>
       </ul>
       <emu-note>
```

The other repair, a StringValue row for `ReservedWord :: one of …` returning CodePointsToString of its code points,
leaves "any |ReservedWord|" quantifying over nodes that do not exist at the site; the wording above avoids that.
(SpecTec applies a companion patch in §22.2.2.9 `CompileToCharSet` rows for `CharacterClassEscape :: D`, `S`, and `W`,
which invoke `<emu-grammar>CharacterClassEscape :: d</emu-grammar>` / `s` / `w` without a Parse Node or the
`_regexpRecord_` argument: `S22.spectec` parses synthetic `"d"`, `"s"`, `"w"` nodes and passes `regexpRecord`.)

## test262

`language/identifiers/val-*-via-escape-hex.js` and `val-*-via-escape-hex4.js` (e.g. `val-if-via-escape-hex4.js`,
`var \u0069\u0066 = 123;`) require the SyntaxError for each unconditionally reserved word. They pass under the proposed
wording; under the literal text the rule is undefined.
