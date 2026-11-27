# Defects in ECMA-262 and non-literal SpecTec readings

Reports of specification defects, ambiguities, and proposed normative changes
recorded when formalizing ECMA-262 in SpecTec (`spec/spectec/`), prepared for
the specification's editors and TC39. Every place where `spec/spectec/` or
`lean/` bakes in a choice other than a literal reading of `spec.html` is
notated here and on the Errata page; items already fixed upstream in the pinned
revision (`b1eaed82f`) and formalization-only representation choices have been
omitted.

- **Revision examined:** tc39/ecma262 at commit `b1eaed82f` (`main` on
  2026-11-12, the pinned revision `external/ecma262`; the section numbers below
  are its own).
- **Tests:** test262 at commit `2e58f87d` (2026-11-11, the pinned revision
  `external/test262`).
- **Engines** (the "Examples" section of each report):
  - V8: Node.js 24.18.1 (V8 13.6.233.17-node.50), `node`;
  - SpiderMonkey: SpiderMonkey 140.13.0, the `js140` shell;
  - JavaScriptCore: Bun 1.3.13 (revision `bf2e2cecf`), whose JavaScriptCore
    is oven-sh/WebKit at `4d5e75eb` (`process.versions.webkit`), `bun`.

  The programs are in [examples/](examples/). A `.js` file is a Script: the
  SpiderMonkey shell runs it as one (`js140 FILE`); Node.js and Bun evaluate it
  with `vm.runInThisContext` in [examples/RESULTS.md](examples/RESULTS.md)'s
  three-line shim (a Script in the main realm). A directory is a Module graph
  whose `main.mjs` runs as a Module (`node main.mjs`, `bun main.mjs`,
  `js140 -m main.mjs`).
- **The formal model:** from the repository root, after `lake build ecma-run`,
  `.lake/build/bin/ecma-run FILE` runs Scripts and (with `--module`) Module
  graphs on its fixed host (`--web-browser` enables Annex B).
- **Upstream:** each report's header has an Upstream item checked against
  `tc39/ecma262`, recorded in [upstream.tsv](upstream.tsv)
  (`scripts/spec_issues_upstream.py`).

## Defects of the text (50)

| # | Clause and step | Kind | What goes wrong | SpecTec reading | Upstream |
|---|---|---|---|---|---|
| [01](01-number-multiply-zero-sign.md) | §6.1.6.1.4 Number::multiply, step 6 | contradiction | `+0 × -5` is +0 by step 6, -0 by the clause's description (IEEE 754) | `proposed` | PR #4072 open |
| [02](02-gather-available-ancestors-empty-cycle-root.md) | §16.2.1.6.1.3.3 GatherAvailableAncestors, step 1.a | failing read | a module whose evaluation threw has an ~empty~ [[CycleRoot]], which step 1.a reads | `literal` | issue #3766 open, PR #3769 open |
| [03](03-builtin-async-return-value.md) | §10.3.3 BuiltinCallOrConstruct, step 10.b.iii | contradiction | `Array.fromAsync` fulfils with *undefined* | `test262` | PR #4074 open |
| [04](04-execute-module-tla-dispose.md) | §16.2.1.7.3.2 ExecuteModule, step 4.b | missing step | top-level `using`/`await using` in a module with top-level await are never disposed | `test262` | issue #4039 open |
| [05](05-parsetext-error-objects.md) | §11.1.6 ParseText, step 5; §22.2.3.4 ParsePattern, step 1.a | missing context / sort | static semantics creates *SyntaxError* objects with no realm and tests undefined sort `error` | `proposed` | issue #3868 open |
| [06](06-dowait-sync-timeout.md) | §25.4.3.14 DoWait, steps 28–31 | contradiction | a timed-out `Atomics.wait` returns *"ok"*; a second wait fails AddWaiter's Assert | `test262` | none found |
| [09](09-atomics-waitasync-timeout-assert.md) | §25.4.3.15 EnqueueAtomicsWaitAsyncTimeoutJob, steps 4 and 1.b.ii | parameter type; failing Assert | HostEnqueueTimeoutJob can get a negative delay, and the Assert fails on integral clocks | `literal` (host clamps delay) | none found |
| [10](10-utc-large-local-time.md) | §21.4.1.18 GetUTCEpochNanoseconds, step 4; §21.4.1.28 MakeDay, step 8 | failing Assert; ambiguity | `new Date(0).setHours(1e21)` fails step 4's Assert; MakeDay's "finite time value" ambiguity | `literal` / `proposed` | PR #3464 open |
| [11](11-regexp-lastindex-inside-surrogate-pair.md) | §22.2.7.2 RegExpBuiltinExec, steps 13.b–28; §22.2.7.6 GetMatchString, step 1 | contradicted result; failing Assert | `/./gu` inside a surrogate pair reports a lone surrogate; `/(?:)/gu` fails GetMatchString's Assert | `literal` (backward 13.b map) | issue #128 open, issue #2511 open |
| [12](12-asyncblockstart-await-result.md) | §27.10.5.2 AsyncBlockStart, steps 3–4 | failing Assert | every async function that awaits resumes with ~empty~, failing step 4's ~unused~ Assert | `test262` | issue #3435 open |
| [13](13-promise-job-abrupt-completion.md) | §9.5 Jobs; §9.5.5 HostEnqueuePromiseJob; §27.5.2.1 NewPromiseReactionJob | contradiction | a promise Job returns a throw completion; a *null*-realm Job runs user species code | `literal` (host preps realm) | none found |
| [14](14-nativefunction-initialname.md) | §20.2.3.5 Function.prototype.toString, step 3 | no result | no NativeFunction has the PropertyName `a b` | `literal` (empty `""` allowed) | PR #2695 open |
| [15](15-synthetic-module-link.md) | §16.2.1.8.4.4 Link of a Synthetic Module Record, steps 1–4 | missing step | a second Link resets a JSON module's exports, observably between two graphs | `literal` | issue #3989 open |
| [20](20-dynamic-function-private-identifiers.md) | §20.2.1.1.1 CreateDynamicFunction, steps 18–29 | missing step; failing Assert | `new Function("o", "return o.#f")` skips `AllPrivateIdentifiersValid` and fails an Assert when called | `proposed` | none found |
| [23](23-races-not-both.md) | §29.8 Races, step 1.a | vacuous condition | "not the case that both A hb B and B hb A" is always true for a strict partial order | `literal` | PR #4021 closed unmerged |
| [24](24-lone-property-gc-assert.md) | §22.2.2.9 CompileToCharSet, step 2 | failing Assert | every lone binary property name (`/\p{Hex}/u`) fails UnicodeMatchPropertyValue's Assert | `test262` | issue #3586 open, PR #3587 open |
| [26](26-annexb-modifiers-early-errors.md) | §B.1.2.1 Early Errors (ExtendedAtom `(?` modifiers) | missing rule | under §B.1.2, `/(?ii:a)/`, `/(?-:a)/` and `/(?i-i:a)/` lack §22.2.1.1's early errors | `test262` | none found |
| [29](29-propname-coverinitializedname.md) | §13.2.5.1 ObjectLiteral early errors; §8.6.5 PropName | missing case | `({a = 1});` asks the PropName of a CoverInitializedName, which has no row | `proposed` | none found |
| [31](31-sort-infinite-comparator.md) | §23.1.3.30.1 SortIndexedProperties, consistent comparator | undefined value | ℝ(±∞) is undefined in the consistent-comparator and sort-order conditions | `test262` | none found |
| [32](32-stringvalue-reservedword.md) | §13.1.1 Identifier early errors | missing case | "the StringValue of any ReservedWord" applies StringValue where no row exists | `test262` | issue #1865 open |
| [33](33-createintrinsics-async-argument-position.md) | §9.3.2 CreateIntrinsics, step 2 | argument position | CreateBuiltinFunction receives `_async_` in `_prefix_`'s parameter position | `test262` | issue #3534 open, issue #4046 open |
| [35](35-contains-awaitexpression-cover.md) | §8.5.1 Contains, step 1.a | missing case | `async function f(x = await 1) {}` has no early error through `CoverAwaitExpression...` | `test262` | none found |
| [36](36-islabelledfunction-labelleditem.md) | §14.13.2 IsLabelledFunction, steps 1–2 | notation | a `Statement` node is never a `LabelledStatement` and has no `LabelledItem` child (§5.1.2) | `test262` | none found |
| [37](37-split-code-units.md) | §22.1.3.23 String.prototype.split, step 10.d | type error | passes a List of code units rather than one-unit Strings to CreateArrayFromList | `test262` | none found |
| [38](38-ordinaryset-receiver-has-property.md) | §10.1.9.2 OrdinarySetWithOwnDescriptor, step 2.d.i | failing Assert | asserts `_receiver_` lacks `_propertyKey_`, failing on hiding Proxies and inherited properties | `proposed` | none found |
| [39](39-must-cover-other-rules.md) | §5.1.5 "must cover", item 4; §15.3.1, §15.9.1 | undefined value | when a cover fails, sibling and ancestor rules read "the \|n\| that is covered by" nothing | `test262` | none found |
| [40](40-annexb-regexp-order-group-count.md) | §B.1.2 Regular Expressions Patterns | ambiguity; self-reference | "previous production alternatives do not match" is undefined; group count is self-referential | `test262` | PR #2445 open |
| [41](41-annexb-html-close-comment-token.md) | §B.1.1 HTML-like Comments with §5.1.3 | missing case | a first-line `-->` (`HTMLCloseComment`) is neither white space nor a comment, becoming an invalid token | `test262` | none found |
| [43](43-allocatesharedarraybuffer-byte-length.md) | §25.2.2.1 AllocateSharedArrayBuffer, step 9.c | type error | growable SharedArrayBuffer passes a Shared Data Block to SetValueInBuffer | `test262` | PR #4023 closed unmerged |
| [44](44-lookahead-source-tokens.md) | §5.1.6.7 Lookahead Restrictions with §12.10 ASI | ambiguity | whether a lookahead restriction reads a semicolon §12.10 inserted (`if (false) let\n[a] = 0;`) | `test262` | none found |
| [45](45-unregister-iterates-cells.md) | §26.2.3.3 FinalizationRegistry.prototype.unregister, step 5 | ambiguity | removes cells from `[[Cells]]` while `For each` iterates it | `test262` | none found |
| [46](46-covered-node-parent.md) | §5.1.5 "must cover", items 2–3; §15.10.1 IsInTailPosition | missing case | a covered node roots a separate parse tree, breaking `return (f(n - 1));` tail calls | `test262` | none found |
| [48](48-init-overlap-equal-ranges.md) | §29.6.6 happens-before, third condition | missing case | orders `~init~` writes only before *overlapping* ranges, excluding equal 1-byte ranges | `literal` | none found |
| [49](49-annexb-ischaracterclass-classcontrolletter.md) | §B.1.2.3 IsCharacterClass | missing case | no `IsCharacterClass` row for `ClassEscape :: c ClassControlLetter` (`/[\c1-\c5]/`) | `test262` | none found |
| [50](50-memory-range-same-block.md) | §29.6.2 reads-bytes-from; §29.7.2 Coherent Reads | missing case | memory ranges omit `[[Block]]`, allowing reads and coherence across distinct blocks | `proposed` | none found |
| [53](53-string-length-overflow.md) | §6.1.4 The String Type; §22.1.3.18 repeat, concat, `+`, join | contradiction | `"ab".repeat(2 ** 52)` and concatenations omit a `> 2^53 - 1` *RangeError* check | `proposed` | none found |
| [55](55-regexp-unicode-escape-lookahead.md) | §22.2.1 Patterns, `RegExpUnicodeEscapeSequence` | ambiguity | escaped surrogate pairs (`/\\uD800\\uDC00+/u`) have two context-free parses | `test262` | none found |
| [56](56-post-asi-lexical-goal.md) | §12 Lexical Grammar; §12.10.1 ASI | contradiction | literal scanning before ASI rejects `let a\n/x/.test("x")` and omits dynamic-function lexical goals | `test262` | none found |
| [57](57-asi-for-lexical-header.md) | §12.10.1 ASI; §14.7.4 `ForStatement`; §5.1.6.7 | missing restriction | `for (let a\n a < 1; a++)` first `;` is inside `LexicalDeclaration`; declarative vs left-to-right ASI | `test262` | none found |
| [58](58-cover-reparse-virtual-semicolons.md) | §5.1.5 "must cover", step 2; §12.10 ASI | missing case | cover reparsing omits virtual `;` inserted inside nested function/class bodies | `test262` | none found |
| [59](59-regexp-exec-end-of-string.md) | §22.2.7.2 RegExpBuiltinExec, step 13.b | undefined index | at `_lastIndex_ = _length_`, step 13.b asks for out-of-bounds `element _lastIndex_ of _string_` | `test262` | none found |
| [60](60-annexb-function-eval-empty.md) | §10.2.11, §16.1.7, §19.2.1.3 Annex B.3.2 vs §15.2.6 | contradiction | B.3.2 replacement steps end with `Return ~unused~` instead of `Return ~empty~` (`eval("{ function f() {} }")`) | `test262` | none found |
| [61](61-annexb-quantifiable-assertion.md) | §B.1.2.5 CompileSubpattern | missing SDO / arity | prose substitution calls undefined 2-arg `CompileAtom` instead of 1-arg `CompileAssertion` on `/(?=a)*/` | `test262` | none found |
| [62](62-annexb-capturing-parens-assert.md) | §22.2.1.2 CountLeftCapturingParensWithin, step 1; §B.1.2.2 | failing Assert | step 1 asserts `#sec-patterns`, failing on every quantified §B.1.2 `ExtendedAtom` | `test262` | none found |
| [63](63-annexb-replacing-and-b33.md) | §B.3.2.1–3, §B.3.3, §B.1.1 | type errors / ambiguity | `Early Errors for _func_` on Function Object, `Contains` on Parse Node, undefined B.3.3 synthetic block | `test262` | none found |
| [64](64-supplemental-covered-by.md) | §13.3.6.1, §15.8.5, §13.15.5 | undefined term | `CallMemberExpression` & `AwaitExpression` lack `"must cover"`; destructuring mismatches cover node | `test262` | none found |
| [65](65-toisostring-year-form.md) | §21.4.4.36 Date.prototype.toISOString, step 7 | underspecification | leaves 4-digit `YYYY` vs expanded `+00YYYY` unspecified for years `0..9999` | `test262` | none found |
| [66](66-module-diamond-circularity-asserts.md) | §16.2.1.7.2.1 GetExportedNames, 3.a; §16.2.1.7.2.2 ResolveExport, 3.a.i | failing Assert | shared mutable visited List triggers circularity `Assert:`s on acyclic diamond `export *` DAGs | `test262` | none found |
| [67](67-memory-model-rmw-cycle.md) | §29.5.4–5, §29.6.5, §29.7.5, §29.5.3 | non-termination / gap | unequal overlapping RMWs cycle infinitely in `ValueOfReadEvent`; unquantified `reads-bytes-from` | `proposed` | none found |
| [68](68-weakref-cells-and-unicode-sorts.md) | §9.9.3 Execution, 1.b; §25.4.3.11, 7; §22.2.2.9.8, 3; §16.2.1.5 | prose / sort defects | single-cell `FinalizationRegistry` loop, `NotifyWaiter` arg (#3328), nonexistent UCD column, `Synthetic Module Record` | `proposed` | issue #3328 open |

## Proposed normative changes (3)

Not defects of internal consistency: the text is consistent, and the proposal changes what it requires.

| # | Clause and step | Kind | What it changes | SpecTec reading | Upstream |
|---|---|---|---|---|---|
| [21](21-identityescape-zwnj-zwj.md) | §22.2.1 Patterns, `IdentityEscape[~UnicodeMode]` | proposal | restores `<ZWNJ>` and `<ZWJ>` as non-Unicode identity escapes after Unicode 15.1 added them to `ID_Continue` | `proposed` | none found |
| [51](51-bigint-maximum-size.md) | §6.1.6.2 BigInt operations; §21.2.2.2 `BigInt.asUintN` | proposal | allows an implementation-defined maximum BigInt size throwing *RangeError* (`$BigIntTooLarge`, 2<sup>30</sup> bits in `Engine`) | `proposed` | issue #4063 closed |
| [54](54-string-maximum-length.md) | §6.1.4 String operations (`repeat`, `padStart`, `concat`, `+`, `join`) | proposal | allows an implementation-defined maximum String length below 2<sup>53</sup> - 1 throwing *RangeError* (`$StringTooLarge`, 2<sup>28</sup> units in `Engine`) | `proposed` | issue #4063 closed |
