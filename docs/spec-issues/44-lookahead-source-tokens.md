# 44. Lookahead restrictions over an automatically inserted semicolon

- **Location:** §5.1.6.7 Lookahead Restrictions (`#sec-lookahead-restrictions`), with §12.10 Automatic Semicolon
  Insertion (`#sec-automatic-semicolon-insertion`) and its §12.10.1 Rules of Automatic Semicolon Insertion
  (`#sec-rules-of-automatic-semicolon-insertion`), rule 1, and §14.5 Expression Statement (`#sec-expression-statement`).
- **Kind:** ambiguity (two readings of "input token sequence"; test262 requires one).
- **Model erratum:** `LookaheadSourceTokens`, default reading test262; its readings: literal, test262, proposed. The
  test262 and proposed readings: a lookahead reads the source's tokens, past the semicolons §12.10 inserted. Under
  the literal reading the run stops where a lookahead reads at an inserted `;`.
- **Upstream:** Checked 2026-11-19: none found (searched for lookahead with "semicolon insertion"). Issue #3269 (open,
  2024-01), "Suggestion: `[no ASI if lookahead ...]` constraint instead of SS rules for OptionalChain", proposes a
  constraint for OptionalChain and does not ask what a lookahead reads after an inserted semicolon.

## Text

§5.1.6.7:

> If the phrase “[lookahead = _seq_]” appears in the right-hand side of a production, it indicates that the
> production may only be used if the token sequence _seq_ is a prefix of the immediately following input token
> sequence.

§12.10 and §12.10.1:

> These situations are described by saying that semicolons are automatically inserted into the source code token
> stream in those situations.

> When, as the source text is parsed from left to right, a token (called the *offending token*) is encountered that
> is not allowed by any production of the grammar, then a semicolon is automatically inserted before the offending
> token if one or more of the following conditions is true: The offending token is separated from the previous token
> by at least one |LineTerminator|. …

§14.5:

> ExpressionStatement[Yield, Await] :
>   [lookahead ∉ { `{`, `function`, `async` [no LineTerminator here] `function`, `class`, `let` `[` }]
>   Expression[+In, ?Yield, ?Await] `;`

## Problem

A lookahead restriction reads "the immediately following input token sequence", and §12.10 describes semicolon
insertion as inserting tokens "into the source code token stream". The text does not say whether a semicolon inserted
by rule 1 is one of the input tokens a later lookahead restriction reads.

Take the Script

```js
if (false) let
[a] = 0;
```

The `[` after `let` is an offending token: `let [` cannot begin an |ExpressionStatement| (its lookahead excludes it),
and a |LexicalDeclaration| cannot be the |Statement| of an |IfStatement|. It is separated from `let` by a line
terminator, so rule 1 inserts `;` before it. If the inserted `;` is an input token, the |ExpressionStatement|'s
lookahead now reads `let` `;`, which is not excluded, so `let;` is an |ExpressionStatement| and `[a] = 0;` another:
the Script is valid. If a lookahead reads the source's tokens, past the inserted semicolon, it still reads `let` `[`
and the production cannot be used: no parse exists and the Script is a SyntaxError.

## Examples

[examples/44-lookahead-inserted-semicolon.js](examples/44-lookahead-inserted-semicolon.js) (outputs:
[RESULTS.md](examples/RESULTS.md#44-lookahead-inserted-semicolonjs)) parses each source as a function body:

```js
var sources = ["if (false) let\n[a] = 0;", "while (false) let\n[a] = 0;", "if (false) let\n{}",
               "if (false) let;\n[a] = 0;"];
for (var s of sources) {
  try { (0, eval)("(function () {\n" + s + "\n})"); print(JSON.stringify(s) + ": no error"); }
  catch (e) { print(JSON.stringify(s) + ": " + e.constructor.name); }
}
```

| | `if … let` LF `[a] = 0;` | `while … let` LF `[a] = 0;` | `if … let` LF `{}` | `if … let;` LF `[a] = 0;` |
|---|---|---|---|---|
| the inserted `;` is an input token | no error | no error | no error | no error |
| lookahead reads the source's tokens | SyntaxError | SyntaxError | no error | no error |
| V8, SpiderMonkey, JavaScriptCore | SyntaxError | SyntaxError | no error | no error |
| formal model (test262 and proposed readings) | SyntaxError | SyntaxError | no error | no error |

Under its literal reading (`ecma-run --erratum LookaheadSourceTokens=literal`) the model's run of the example stops
at the first source (`stop: residue formal-parsetextin#0 2`), and so does its run of `if (0) let` LF `[a] = 0;`
(`tests/run/erratum_lookahead_source_tokens_literal.js`); under the default reading that Script is a SyntaxError
(`tests/run/erratum_lookahead_source_tokens.js`: `throw: SyntaxError`).

## Proposed wording

Proposed: a paragraph in §12.10.1, after the rules and their overriding condition:

```diff
--- a/spec.html
+++ b/spec.html
@@ -18089,1 +18089,2 @@
       <p>However, there is an additional overriding condition on the preceding rules: a semicolon is never inserted automatically if the semicolon would then be parsed as an empty statement or if that semicolon would become one of the two semicolons in the header of a `for` statement (see <emu-xref href="#sec-for-statement"></emu-xref>).</p>
+      <p>A semicolon inserted by these rules is not a token of the input token sequence that a lookahead restriction (<emu-xref href="#sec-lookahead-restrictions"></emu-xref>) examines.</p>
```

Or state in §5.1.6.7 that the input token sequence a lookahead restriction examines is the source text's tokens,
without automatically inserted semicolons.

## test262

language/statements/{do-while,for,for-await-of,for-in,for-of,if,labeled,while,with}/let-array-with-newline.js (9
files) require a SyntaxError at parse time for this pattern: the second reading.
