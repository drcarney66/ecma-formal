# 26. Annex B: `/(?ii:a)/` has no early error under §B.1.2

- **Location:** §B.1.2.1 Static Semantics: Early Errors (`#sec-patterns-static-semantics-early-errors-annexb`),
  against §22.2.1.1 Static Semantics: Early Errors (`#sec-patterns-static-semantics-early-errors`) and the
  ExtendedAtom productions of §B.1.2 (`#sec-regular-expressions-patterns`); §B.1.2.7 Runtime Semantics: CompileAtom
  (`#sec-compileatom-annexb`).
- **Kind:** missing rule (early errors that the main grammar has and the Annex B grammar loses).
- **Model erratum:** `AnnexBModifierEarlyErrors`, baked-in SpecTec reading test262 (`spec/spectec/08-early-errors.spectec`);
  its readings: literal, test262, proposed. The test262 and proposed readings apply §22.2.1.1's five modifier rules to
  the ExtendedAtom productions too (without which `/(?i-i:a)/` on a `--web-browser` host also reaches `UpdateModifiers`
  step 1's disjointness `Assert:`).
- **Upstream:** Checked 2026-11-19: none found (searched for "RegularExpressionModifiers" and for modifiers with
  "Annex B"). The modifiers came with PR #3221 (merged 2025-01, commit f55b18095), "Normative: Add RegExp Modifiers",
  which added the productions to both grammars and their early errors to §22.2.1.1 only.

## Text

§22.2.1.1:

> Atom :: `(?` RegularExpressionModifiers `:` Disjunction `)`
> - It is a Syntax Error if the source text matched by |RegularExpressionModifiers| contains the same code point more
>   than once.
>
> Atom :: `(?` RegularExpressionModifiers `-` RegularExpressionModifiers `:` Disjunction `)`
> - It is a Syntax Error if the source text matched by the first |RegularExpressionModifiers| and the source text
>   matched by the second |RegularExpressionModifiers| are both empty.
> - It is a Syntax Error if the source text matched by the first |RegularExpressionModifiers| contains the same code
>   point more than once.
> - It is a Syntax Error if the source text matched by the second |RegularExpressionModifiers| contains the same code
>   point more than once.
> - It is a Syntax Error if any code point in the source text matched by the first |RegularExpressionModifiers| is
>   also contained in the source text matched by the second |RegularExpressionModifiers|.

§B.1.2 replaces Term[~UnicodeMode] by alternatives over ExtendedAtom, which has its own

> ExtendedAtom[NamedCaptureGroups] ::
>   …
>   `(?` RegularExpressionModifiers `:` Disjunction[~UnicodeMode, ~UnicodeSetsMode, ?NamedCaptureGroups] `)`
>   `(?` RegularExpressionModifiers `-` RegularExpressionModifiers `:` Disjunction[~UnicodeMode, ~UnicodeSetsMode,
>   ?NamedCaptureGroups] `)`

§B.1.2.1 begins

> The semantics of … is extended as follows:

and adds rules for ExtendedAtom :: InvalidBracedQuantifier and the two class-range productions only. §B.1.2.7 (CompileAtom) carries the Atom rules over:

> Rules for the |Atom| productions except for Atom :: PatternCharacter are also used for the |ExtendedAtom|
> productions, but with |ExtendedAtom| substituted for |Atom|.

## Problem

Without the `u` or `v` flag, on a host that implements §B.1.2 (every web browser), a pattern parses with §B.1.2's
grammar, where `(?ii:a)` is an ExtendedAtom, not an Atom. No rule of §22.2.1.1 applies to it and §B.1.2.1 adds none,
so `/(?ii:a)/`, `/(?-:a)/` and `/(?i-i:a)/` are valid patterns there, and §B.1.2.7 gives them CompileAtom's meaning.
Under the main grammar (a host without §B.1.2, or with the `u` flag) they are SyntaxErrors. Nothing suggests that
Annex B meant to relax the modifiers: its other additions concern legacy syntax, and the modifiers came after it.

## Examples

[examples/26-annexb-modifiers-early-errors.js](examples/26-annexb-modifiers-early-errors.js) (outputs:
[RESULTS.md](examples/RESULTS.md#26-annexb-modifiers-early-errorsjs)) compiles each pattern as a literal (indirect
eval) and with the RegExp constructor:

```js
var patterns = ["(?ii:a)", "(?-:a)", "(?i-i:a)", "(?i:a)", "(?i-m:a)"];
for (var p of patterns) {
  var lit, ctor;
  try { (0, eval)("/" + p + "/"); lit = "no error"; } catch (e) { lit = e.constructor.name; }
  try { new RegExp(p); ctor = "no error"; } catch (e) { ctor = e.constructor.name; }
  print("/" + p + "/: " + lit + "; new RegExp: " + ctor);
}
```

| | `(?ii:a)`, `(?-:a)`, `(?i-i:a)` | `(?i:a)`, `(?i-m:a)` |
|---|---|---|
| literal text, §B.1.2 | no error | no error |
| literal text, main grammar | `SyntaxError` | no error |
| V8, SpiderMonkey, JavaScriptCore (§B.1.2 hosts) | `SyntaxError` | no error |
| formal model (main grammar; literal, test262 and proposed readings) | `SyntaxError` | no error |

## Proposed wording

Proposed: the rules carried over in §B.1.2.1, as §B.1.2.7 does for CompileAtom:

```diff
--- a/spec.html
+++ b/spec.html
@@ -53962,6 +53962,7 @@
       <emu-annex id="sec-patterns-static-semantics-early-errors-annexb">
         <h1>Static Semantics: Early Errors</h1>
         <p>The semantics of <emu-xref href="#sec-patterns-static-semantics-early-errors"></emu-xref> is extended as follows:</p>
+        <p>Rules for the <emu-grammar>Atom :: `(?` RegularExpressionModifiers `:` Disjunction `)`</emu-grammar> and <emu-grammar>Atom :: `(?` RegularExpressionModifiers `-` RegularExpressionModifiers `:` Disjunction `)`</emu-grammar> productions are also used for the corresponding |ExtendedAtom| productions, but with |ExtendedAtom| substituted for |Atom|.</p>
         <emu-grammar>ExtendedAtom :: InvalidBracedQuantifier</emu-grammar>
         <ul>
           <li>
```

## test262

`language/literals/regexp/early-err-modifiers-*.js` (25 files), `built-ins/RegExp/early-err-modifiers-*.js` (22) and
`built-ins/RegExp/syntax-err-arithmetic-modifiers-*.js` (55), all outside `annexB/`, require a *SyntaxError* for `/(?ii:a)/` and
its siblings without the `u` flag. A host that implements §B.1.2 fails them under the literal text.
