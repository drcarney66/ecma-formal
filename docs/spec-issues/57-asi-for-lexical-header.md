# 57. ASI in `for ( LexicalDeclaration … )` headers, left-to-right prefix order, and `[no LineTerminator here]` in lookahead sets

- **Location:** §12.10.1 Rules of Automatic Semicolon Insertion (`#sec-rules-of-automatic-semicolon-insertion`),
  overriding condition; §14.7.4 The `for` Statement (`#sec-for-statement`); §5.1.5 The Syntactic Grammar
  (`#sec-syntactic-grammar`); §5.1.6.7 Lookahead Restrictions (`#sec-lookahead-restrictions`).
- **Kind:** missing restriction and grammar-formalism gap (`ForStatement`'s `LexicalDeclaration` owns the first header
  `;`, §5.1.5's declarative ASI conflicts with §12.10.1's left-to-right rule, and `[no LineTerminator here]` inside a
  lookahead set is undefined in §5.1.6.7).
- **Model erratum:** `ForLexicalHeaderASI`, baked-in SpecTec reading test262 (layer `parser`, `ForHeadersExplicit`,
  `ValidASI`, and `LookItem.noLT` in `spec/spectec/prose/04-derives.spectec`). SpecTec forbids virtual `;` as the final
  token of a `LexicalDeclaration` child of `ForStatement`, formalizes left-to-right maximal viable prefix ASI, and
  defines `LookItem.noLT` inside lookahead sequences.
- **Upstream:** Checked 2026-11-19: none found (searched for "header of a `for` statement" with "LexicalDeclaration").

## Text

§12.10.1:

> However, there is an additional overriding condition on the preceding rules: a semicolon is never inserted automatically if the semicolon would then be parsed as an empty statement or if that semicolon would become one of the two semicolons in the header of a `for` statement

§14.7.4:

> ForStatement[Yield, Await, Return] :
>   `for` `(` [lookahead != `let` `[`] Expression[~In, ?Yield, ?Await]? `;` Expression[+In, ?Yield, ?Await]? `;` Expression[+In, ?Yield, ?Await]? `)` Statement[?Yield, ?Await, ?Return]
>   `for` `(` `var` VariableDeclarationList[~In, ?Yield, ?Await] `;` Expression[+In, ?Yield, ?Await]? `;` Expression[+In, ?Yield, ?Await]? `)` Statement[?Yield, ?Await, ?Return]
>   `for` `(` LexicalDeclaration[~In, ?Yield, ?Await] Expression[+In, ?Yield, ?Await]? `;` Expression[+In, ?Yield, ?Await]? `)` Statement[?Yield, ?Await, ?Return]

## Problem

1. **`for ( LexicalDeclaration … )` first semicolon.** In the third `ForStatement` production, `ForStatement` itself has
   only *one* `;` terminal on its right-hand side — the first semicolon of `for (let a = 1; a < 2; a++)` is the trailing
   `;` inside `LexicalDeclaration : LetOrConst BindingList ;` (or `UsingDeclaration` / `AwaitUsingDeclaration`), where
   ASI is normally permitted! Read literally on productions, `for (let a\n a < 1; a++) {}` inserts `;` at the end of
   `LexicalDeclaration`.
2. **Declarative (§5.1.5) vs left-to-right (§12.10.1) ASI.** §5.1.5 describes ASI declaratively (*"if only semicolons
   were added to the sequence in certain places"*), under which `a = b\n+c` has two parses (`a = b + c;` vs `a = b; +c;`)
   and `let a;\na\n[\n] = [];` parses by inserting `;` after `a`, whereas all engines commit left-to-right to the
   longest viable prefix.
3. **`[no LineTerminator here]` inside lookahead sets.** `ExpressionStatement` and `ExportDeclaration` write
   `` `async` [no LineTerminator here] `function` `` inside `[lookahead ∉ { … }]`, whereas §5.1.6.7 defines lookahead
   elements solely as token sequences and §5.1.6.6 defines `[no LineTerminator here]` only on production right-hand sides.

## Examples

```js
var bad = ["for (let a\n a < 1; a++) {}", "let a;\na\n[\n] = [];"];
for (var s of bad) {
  try { (0, eval)(s); print("valid"); } catch (e) { print(e.name); }
}
```

| | `for (let a` LF `a < 1; a++) {}` | `let a; a` LF `[` LF `] = [];` |
|---|---|---|
| literal §14.7.4 / declarative §5.1.5 | valid | valid (`a; [] = [];`) |
| V8, SpiderMonkey, JavaScriptCore | `SyntaxError` | `SyntaxError` |
| formal model (test262 reading) | `SyntaxError` | `SyntaxError` |

## Proposed wording

Amend §12.10.1's overriding condition to include the terminating semicolon of a `|LexicalDeclaration|` in a
`|ForStatement|` header, define offending-token ASI via maximal viable left-to-right prefix continuation, and define
`[no LineTerminator here]` between adjacent tokens in §5.1.6.7 lookahead sequences.

## test262

`language/asi/S7.9_A5.2_T1.js` and `language/statements/for/` require `SyntaxError` when either semicolon in a `for`
header is omitted across a newline.
