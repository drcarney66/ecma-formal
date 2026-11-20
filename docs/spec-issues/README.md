# Defects in ECMA-262 found by a step-by-step formalization

Reports of defects in the text of ECMA-262, for the specification's editors
and TC39. They come from a formal model that follows the specification
algorithm by algorithm and step by step. Each report argues from the text
alone, gives small programs whose behaviour shows the problem, and proposes a
change. None of them has been filed with TC39.

- **Revision examined:** tc39/ecma262 at commit `b1eaed82f` (`main` on
  2026-11-12, the pinned revision `external/ecma262`, and still `main` on
  2026-11-19; the section numbers below are its own).
- **Tests:** test262 at commit `2e58f87d` (2026-11-11, the pinned revision
  `external/test262`).
- **Engines** (the "Examples" section of each report):
  - V8: Node.js 24.18.1 (V8 13.6.233.17-node.50), `node`;
  - SpiderMonkey: SpiderMonkey 140.13.0, the `js140` shell;
  - JavaScriptCore: Bun 1.3.13 (revision `bf2e2cecf`), whose JavaScriptCore
    is oven-sh/WebKit at `4d5e75eb` (`process.versions.webkit`), `bun`.

  The programs are in [examples/](examples/). A `.js` file is a Script: the
  SpiderMonkey shell runs it as one (`js140 FILE`); Node.js and Bun would run
  it as CommonJS or as a Module, so they run a three-line shim (in RESULTS.md) that evaluates
  it with `vm.runInThisContext`, a Script in the main realm (sloppy mode,
  `this` the global object, Annex B). A directory is a Module graph: its
  `main.mjs` runs as a Module (`node main.mjs`, `bun main.mjs`,
  `js140 -m main.mjs`). The programs define `print` as `console.log` when it
  is missing. The SpiderMonkey 140 shell needs `-P atomics_wait_async=true`
  for 09 and `--enable-import-attributes` for 15; RESULTS.md has its runs
  with and without them (and of 04 with and without
  `--enable-explicit-resource-management`). Every output quoted in the reports, with exit statuses and
  error output, is in [examples/RESULTS.md](examples/RESULTS.md), which
  `scripts/spec_issues_run.py` writes from fresh runs of every example on the
  three engines and the model. The engines come from the flake's `engines`
  dev shell (`flake.nix`); from the repository root:

  ```
  nix develop .#engines --profile ~/.local/state/ecma-formal/devshell-engines-jsc -c true
  nix develop ~/.local/state/ecma-formal/devshell-engines-jsc -c python3 scripts/spec_issues_run.py
  ```

  (The first command makes the profile, the second reruns everything; build
  the model first, below.)
- **The formal model:** from the repository root, after
  `lake build ecma-run`, `.lake/build/bin/ecma-run FILE`: the machine,
  Scripts and (with `--module`) Module graphs, on its fixed host. It first prints the Script's
  completion (`normal: …`); the reports omit that line. RESULTS.md's model
  outputs were last rerun on 2026-11-19 (commit `2eaba4f`), on the pinned
  text.
- **Upstream:** each report's header has an Upstream item: what a check of
  tc39/ecma262 found on 2026-11-19 (the issues and pull requests that report,
  fix or relate to the defect, with their state on that day, and the commits
  that changed the text). The record of that check is
  [upstream.tsv](upstream.tsv) (`scripts/spec_issues_upstream.py`); the
  Upstream column below gives the first of them, or the fix. Four were fixed
  before the pinned revision; see [Fixed upstream](#fixed-upstream).

## Summary

| # | Clause and step | Kind | What goes wrong | test262 | Upstream |
|---|---|---|---|---|---|
| [01](01-number-multiply-zero-sign.md) | §6.1.6.1.4 Number::multiply, step 6 | contradiction | `+0 × -5` is +0 by step 6, -0 by the clause's description (IEEE 754) | none (S11.5.1_A4_T2's description states the IEEE rule; no assertion covers the case) | PR #4072 open |
| [02](02-gather-available-ancestors-empty-cycle-root.md) | §16.2.1.6.1.3.3 GatherAvailableAncestors, step 1.a | failing read | a module whose evaluation threw has an ~empty~ [[CycleRoot]], which the step reads | none | issue #3766 open, PR #3769 open |
| [03](03-builtin-async-return-value.md) | §10.3.3 BuiltinCallOrConstruct, step 10.b.iii | contradiction | `Array.fromAsync` fulfils with *undefined* | fromAsync tests | PR #4074 open |
| [04](04-execute-module-tla-dispose.md) | §16.2.1.7.3.2 ExecuteModule, step 4.b | missing step | top-level `using`/`await using` in a module with top-level await are never disposed | await-using tests | issue #4039 open, PR #4007 closed unmerged |
| [05](05-parsetext-error-objects.md) | §11.1.6 ParseText, step 5; §22.2.3.4 ParsePattern, step 1.a | missing context | a static semantics creates objects with no realm | none (unobservable) | none found |
| [06](06-dowait-sync-timeout.md) | §25.4.3.14 DoWait, steps 28–31 | contradiction | a timed-out `Atomics.wait` returns *"ok"*; a second wait fails an Assert | Atomics.wait tests | none found |
| [09](09-atomics-waitasync-timeout-assert.md) | §25.4.3.15 EnqueueAtomicsWaitAsyncTimeoutJob, steps 4 and 1.b.ii | parameter type; failing Assert | HostEnqueueTimeoutJob can get a negative delay, and the Assert depends on implementation-defined choices | none | none found |
| [10](10-utc-large-local-time.md) | §21.4.1.18 GetUTCEpochNanoseconds, step 4 (from §21.4.1.26 UTC) | failing Assert; ambiguity | `new Date(0).setHours(1e21)`; MakeDay's "finite time value" makes `Date.UTC(275761, 0, -256)` *NaN* or a date (the engines: a date) | none | PR #3464 open |
| [11](11-regexp-lastindex-inside-surrogate-pair.md) | §22.2.7.2 RegExpBuiltinExec, steps 13.b–24; §22.2.7.6 GetMatchString, step 1 | contradicted result; failing Assert | `/./gu` with `lastIndex` inside a surrogate pair reports index 1 and a lone surrogate; `/(?:)/gu` builds a Match Record that ends before it starts | none | issue #128 open, issue #2511 open |
| [12](12-asyncblockstart-await-result.md) | §27.10.5.2 AsyncBlockStart, steps 3–4 (with §27.10.5.3 Await, step 8) | failing Assert | every async function that awaits: Await resumes the block with ~empty~, the Assert expects ~unused~ | none (an Assert is not observable) | issue #3435 open |
| [13](13-promise-job-abrupt-completion.md) | §9.5 Jobs; §27.5.2.1 NewPromiseReactionJob, steps 1.h.i, 1.i, 2 | contradiction | a promise Job returns a throw completion; a *null*-realm Job runs code | none | none found |
| [14](14-nativefunction-initialname.md) | §20.2.3.5 Function.prototype.toString, step 3 | no result | no NativeFunction has the PropertyName `a b` | none | related: PR #2695 open |
| [15](15-synthetic-module-link.md) | §16.2.1.8.4.4 Link of a Synthetic Module Record, steps 1–4 | missing step | a second Link resets a JSON module's exports, observably between two graphs | none | issue #3989 open |
| [19](19-other-questions.md) | several | editorial / clarification | HostLoadImportedModule "each time"; ShallowestContainedJSONValue and covers; ECMA-404 surrogates; a timeout past the last time value; Execution's cell; nine grammar questions | none | none found |
| [20](20-dynamic-function-private-identifiers.md) | §20.2.1.1.1 CreateDynamicFunction, steps 18–29 | missing step; failing Assert | `new Function("o", "return o.#f")` is not a SyntaxError; its call fails MakePrivateReference's Assert | private-identifiers-not-empty.js | none found |
| [21](21-identityescape-zwnj-zwj.md) | §22.2.1 Patterns, IdentityEscape[~UnicodeMode] | contradiction | since Unicode 15.1 made U+200C and U+200D ID_Continue, `\` ZWNJ and `\` ZWJ are SyntaxErrors without the `u` flag (main grammar) | S7.8.5_A1.4_T2.js, S7.8.5_A2.4_T2.js | none found |
| [23](23-races-not-both.md) | §29.8 Races, step 1.a | vacuous condition | "not the case that both A hb B and B hb A" is always true for a strict partial order, so ordered conflicting events race (likely "neither … nor"; the model reads the literal text) | none | PR #4021 closed unmerged |
| [24](24-lone-property-gc-assert.md) | §22.2.2.9 CompileToCharSet, LoneUnicodePropertyNameOrValue, step 2 | failing Assert | every lone binary property name (`/\p{Hex}/u`) reaches UnicodeMatchPropertyValue's Assert | property-escapes/generated/ (53 binary-property files; none fails) | issue #3586 open, PR #3587 open |
| [25](25-number-shift-result.md) | §6.1.6.1.9–11 Number::leftShift, signedRightShift, unsignedRightShift, step 4; §6.1.6.1.2 Number::bitwiseNOT, step 2 | editorial (irregular step) | the shifts and NOT name operations on Numbers the spec never defines; only the range sentence fixes the 32-bit view (`1 << 31` is -2<sup>31</sup>) | left-shift/S11.7.1_A4_T4.js (#994) | PR #2274 open, a draft |
| [26](26-annexb-modifiers-early-errors.md) | §B.1.2.1 Early Errors (ExtendedAtom `(?` modifiers) | missing rule | under §B.1.2, `/(?ii:a)/`, `/(?-:a)/` and `/(?i-i:a)/` have no early error, since the modifier rules of §22.2.1.1 are keyed on Atom | language/literals/regexp/early-err-modifiers-*.js, built-ins/RegExp/early-err-modifiers-*.js | none found |
| [27](27-numerictorawbytes-encoding-steps.md) | §25.1.3.17 NumericToRawBytes, steps 1.a, 2.a, 3.a, 4.d.i, 4.e.i | editorial (irregular steps) | the byte order and the NaN latitude are sentences after the step's expression; "each implementation distinguishable NaN value" against §6.1.6.1's single NaN | none (no observable difference) | issue #3567 open |
| [28](28-tobigint-boolean-literals.md) | §7.1.15 ToBigInt, the BigInt Conversions table's Boolean row | editorial (notation) | the results are source-text literals `1n`/`0n` and the two cases one sentence, unlike every other BigInt value and step | none (no observable difference) | none found |
| [29](29-propname-coverinitializedname.md) | §13.2.5.1 ObjectLiteral early errors (`__proto__` rule); §8.6.5 PropName | missing case; editorial (no erratum of the model) | `({a = 1});` asks the PropName of a CoverInitializedName, which has none (unobservable) | cover-initialized-name.js | none found |
| [31](31-sort-infinite-comparator.md) | §23.1.3.30.1 SortIndexedProperties, the consistent comparator definition | undefined value | a comparator result of ±∞ has no ℝ, so none of _a_ &lt;<sub>C</sub> _b_, =<sub>C</sub>, &gt;<sub>C</sub> holds and whether the comparator is consistent is undecided | none | none found |
| [32](32-stringvalue-reservedword.md) | §13.1.1 Identifier early errors (`IdentifierName but not ReservedWord`) | missing case | "the StringValue of any ReservedWord" applies StringValue to productions it has no row for | language/identifiers/val-*-via-escape-*.js | issue #1865 open |
| [33](33-createintrinsics-async-argument-position.md) | §9.3.2 CreateIntrinsics, step 2 | argument position | the CreateBuiltinFunction call passes _async_ in _prefix_'s position and passes no _prefix_: literally, `Array.fromAsync` gets [[Async]] *false* | built-ins/Array/fromAsync/ | issue #3534 open, issue #4046 open |
| [35](35-contains-awaitexpression-cover.md) | §8.5.1 Contains, step 1.a (no row for UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead) | missing case | `async function f(x = await 1) {}` has no early error: no Parse Node is an instance of AwaitExpression, so the six "Contains \|AwaitExpression\|" rules never apply | instance-await-expr-in-param.js, early-errors-expression-formals-contains-await-expr.js, await-as-param-nested-arrow-body-position.js | none found |
| [36](36-islabelledfunction-labelleditem.md) | §14.13.2 IsLabelledFunction, steps 1–2 | notation | a Statement node is never a LabelledStatement and has no LabelledItem child (§5.1.2), so literally `if (1) l: function f() {}` is valid | language/statements/*/labelled-fn-stmt*.js (18 files) | none found |
| [37](37-split-code-units.md) | §22.1.3.23 String.prototype.split, step 10.d | type error | with an empty separator, the List passed to CreateArrayFromList holds code units, which are not ECMAScript language values; test262 requires one-code-unit Strings | separator-empty-string-instance-is-string.js | none found |
| [38](38-ordinaryset-receiver-has-property.md) | §10.1.9.2 OrdinarySetWithOwnDescriptor, step 2.d.i | failing Assert; editorial (no erratum of the model) | after a Proxy receiver's trap answers *undefined* for a property its target has, "_receiver_ does not currently have a property" is vacuous on the receiver's own storage and false through the Proxy | none | none found |
| [39](39-must-cover-other-rules.md) | §5.1.5 "must cover", item 4; the ArrowFunction and AsyncArrowFunction early errors | undefined value; clarification (no erratum of the model) | when a cover does not cover its \|n\|, the other rules of the production and those above it (Contains, BoundNames, IsSimpleParameterList through the cover) read "the \|n\| that is covered by" a node that does not exist | arrow-function/dstr/*ary-ptrn-rest-{init,not-final}-*.js, async-arrow-function/dflt-params-rest.js, early-errors-arrow-formals-lineterminator.js | none found |
| [40](40-annexb-regexp-order-group-count.md) | §B.1.2 Regular Expressions Patterns (the ordering sentence; AtomEscape's group-number condition) | ambiguity; self-reference | "each alternative is considered only if previous production alternatives do not match" has no defined meaning over §5.1's parses, and the condition counts the groups of the Pattern it is choosing | annexB/built-ins/RegExp, annexB/language/literals/regexp/legacy-octal-escape.js | PR #2445 open |
| [41](41-annexb-html-close-comment-token.md) | §B.1.1 HTML-like Comments (InputElementHashbangOrRegExp :: HTMLCloseComment) with §5.1.3 | missing case | an HTMLCloseComment input element is neither white space nor a comment, so §5.1.3 makes it a token the syntactic grammar has no terminal for: a first line `--> a comment` is a SyntaxError | annexB/language/comments/single-line-html-close-first-line-{1,2,3}.js (test262 PR #4002) | none found |
| [42](42-annexb-module-goal-reparse.md) | §B.1.1 HTML-like Comments (the Module condition), §17.1, with §5.1.5 | clarification | the condition names the goal symbol \|Module\|; the reparses of tokens within a Module are outside B.1.1 only through §5.1.5's word "tokens", so a rescan of a cover's text has to carry the Module context (`(a <!--b)`) | none | none found |
| [43](43-allocatesharedarraybuffer-byte-length.md) | §25.2.2.1 AllocateSharedArrayBuffer, step 9.c | type error | a growable SharedArrayBuffer's length is stored with SetValueInBuffer on a Shared Data Block, which takes a buffer object | 19 files construct a growable SharedArrayBuffer (built-ins/SharedArrayBuffer, Atomics, staging) | PR #4023 closed unmerged |
| [44](44-lookahead-source-tokens.md) | §5.1.6.7 Lookahead Restrictions with §12.10 ASI, rule 1 (§14.5's `let` `[` lookahead) | ambiguity | whether a lookahead reads a semicolon that §12.10 inserted: `if (false) let` LF `[a] = 0;` is valid if it does, a SyntaxError if it reads the source's tokens (the engines) | language/statements/*/let-array-with-newline.js (9 files) | none found |
| [45](45-unregister-iterates-cells.md) | §26.2.3.3 FinalizationRegistry.prototype.unregister, step 5 | ambiguity | step 5 removes cells from the List it iterates, and For each does not say what it visits then: walked by position, the second of two cells in a row with the token stays | unregister-object-token.js, unregister-symbol-token.js | none found |
| [46](46-covered-node-parent.md) | §5.1.5 "must cover", items 2–3; §15.10.1 IsInTailPosition, steps 2–3 | missing case | a covered node is the root of its own tree, so `return (f(n - 1));` is not in a FunctionBody and is not a tail call | language/expressions/tco-pos.js | none found |
| [47](47-promise-job-null-realm-code.md) | §9.5.5 HostEnqueuePromiseJob, its note; §27.5.2.1 NewPromiseReactionJob, steps 1.i, 2–3 | contradiction; editorial (no erratum of the model) | a *null*-realm Job calls the derived promise's resolving functions, which are user code when a species constructor provides them; the note says it calls none | none | none found |
| [48](48-init-overlap-equal-ranges.md) | §29.6.6 happens-before, the third condition, with §29.1's "overlapping" | missing case | an ~init~ write is ordered only before events with *overlapping* ranges, and §29.1's definition excludes equal ranges, so a 1-byte access is unordered with its block's ~init~ write | none | none found |
| [49](49-annexb-ischaracterclass-classcontrolletter.md) | §B.1.2.3 IsCharacterClass, with §B.1.2's `[~UnicodeMode] c ClassControlLetter` and §B.1.2.1's range rules | missing case | the range rules ask IsCharacterClass of `\c1` in `/[\c1-\c5]/`, and no clause defines it for `ClassEscape :: c ClassControlLetter` | none | none found |
| [50](50-memory-range-same-block.md) | §29.6.2 reads-bytes-from, the first condition; §29.7.2 Coherent Reads, step 1.c.ii | missing case | a memory range is a Set of byte indices with no [[Block]], so a read may read, and coherence is judged against, writes to another block at the same index; with two blocks in one agent a read returns the other block's byte | none | none found |
| [52](52-mv-decimalintegerliteral-zero.md) | §12.9.3.2 Static Semantics: MV, the row for `` DecimalIntegerLiteral :: `0` `` | editorial (stale row) | PR #3988 made \|DecimalIntegerLiteral\|'s first alternative \|DecimalDigit\| and left the row, which names a production the grammar no longer has (nothing observable: `0` is 0 through the chain production) | none | none found |
| [53](53-string-maximum-length.md) | §6.1.4 The String Type; §22.1.3.16 repeat, step 7; StringPaddingBuiltinsImpl, step 7; concat, step 5.b; ApplyStringOrNumericBinaryOperator, step 1.c.iii; JoinIndexedProperties, steps 4.a, 4.d.iii | missing limit | Strings can be constructed up to length 2<sup>53</sup> - 1; every engine throws a *RangeError* past its smaller implementation limit, left unspecified in the text | none | issue #4063 closed |

Kinds: a *contradiction* is a step whose literal result disagrees with another
normative statement of the specification; *no result* and *missing step* mean
the text defines no behaviour (or omits one it clearly intends); a *failing
Assert* or *failing `!`* is an assertion that a conforming execution can make
false. A kind marked *no erratum of the model* (29, 38, 39, 47) is an editorial
or clarification report: the model reads the text there by a register row of
spec/formal/decisions.md, and nothing it runs depends on the report.

## Fixed upstream

Fixed in `b1eaed82f`; the model's errata are retired and the reports stay, as
records, with a line saying so:

- [07](07-typedarray-with-filter-bang.md): TypedArrayWithSetElementAbrupt and
  TypedArrayFilterKeptUndefined, by 4feb0272b (PR #3979).
- [08](08-islooselyequal-boolean-bang.md): IsLooselyEqualBooleanAbrupt, by
  8a3e4aae (PR #4067).
- [22](22-reads-bytes-from-unbound-result.md): ReadsBytesFromUnboundResult, by
  d8cb8772 (PR #4064).
- [34](34-revalidate-atomic-access.md): RevalidateAtomicAccess, by 5e0f8b33
  (PR #3926, issue #3924).

## A proposed normative change

Not a defect: the text is consistent, and the proposal changes what it
requires.

| # | Clause and step | Kind | What it changes | test262 | Upstream |
|---|---|---|---|---|---|
| [51](51-bigint-maximum-size.md) | §6.1.6.2 The BigInt Type; §6.1.6.2.3 exponentiate, step 3; §6.1.6.2.4 multiply, step 1; §6.1.6.2.7–8 add/subtract, step 1; §6.1.6.2.9 leftShift, step 2; §21.2.2.2 asUintN, step 3 | proposal | a BigInt "may be any size", so `2n ** (2n ** 40n)` has an exact result; implementations throw a *RangeError* past a maximum size (V8: 2<sup>30</sup> bits), which the proposal allows | none found | none found |

## How the model resolves each defect

Each erratum is an `emu-erratum` in `spec/formal/readings.emu` (38 at
`b1eaed82f`, listed in `spec/formal/errata.txt`: 36 defects of the text and
two proposals), with its resolution (`literal`, `test262`, `proposed` or
`pending`) and the readings it applies.
