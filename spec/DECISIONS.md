# SpecTec Formalization Decisions Register
This document records every design decision, ambiguity resolution, active reading choice, prose-step formalization, model choice, host default, and structural translation decision made when eliminating the `.emu` overlay layer (`spec/formal/*.emu`) and translating the ECMA-262 formal specification (`external/ecma262`, pinned commit `b1eaed82f`) into pure SpecTec (`spec/spectec/`).
> [!NOTE]
> Unlike the legacy `.emu` overlay, SpecTec bakes in **one** single resolved specification instead of carrying runtime errata toggles (`<emu-reading>`, `Ins.readings`, `Expr.prose`, `<emu-phrase>`), prose fallback channels, or HTML/SHA-256 overlays. Whenever a pinned ECMA-262 passage admitted multiple readings (errata vs. literal text, proposed fixes, undefined prose predicates, or ambiguous wording), the active reading was baked into SpecTec. Every such decision — together with alternatives and where the baked-in choice could be wrong — is documented below.
## Table of Contents
1. [Active Errata, Non-Literal SpecTec Readings & Proposed Changes (56 entries)](#1-active-errata--proposed-normative-changes)
2. [Grammar Readings, Rule Patches & Parser-Layer Choices](#2-grammar-readings-rule-patches--parser-layer-choices)
3. [Baked-in Prose-Step Formalizations (`definition` readings)](#3-baked-in-prose-step-formalizations)
4. [Unchecked Assertions & Constructive Choices](#4-unchecked-assertions--constructive-choices)
5. [Interpreting Readings & Interpreting Phrase Meanings](#5-interpreting-readings--interpreting-phrase-meanings)
6. [Model Choices](#6-model-choices)
7. [Host-Choice Defaults](#7-host-choice-defaults)
8. [Data Sort Doubts & Ambiguities](#8-data-sort-doubts--ambiguities)
9. [SpecTec Translation & AST Simplifications](#9-spectec-translation--ast-simplifications)

## 1. Active Errata & Proposed Normative Changes
SpecTec tracks **56** active specification defects, non-literal prose readings, and proposed normative changes (53 defects/non-literal readings and 3 proposed normative changes). Runtime `ErratumId` switching is absent: each item's chosen reading (`test262`, `proposed`, or `literal`) is baked directly into `spec/spectec/` and `lean/`.

**How baked-in resolution works**:
- `test262` / `proposed`: the non-literal reading or proposed fix is baked into `spec/spectec/` (or `lean/`) so the formal specification and reference engine are well-defined.
- `literal`: the literal ECMA-262 wording is kept in SpecTec; remarks note any companion host/sort choices and where literal execution stops.

**Summary Table:**

| Erratum | Kind | Baked-In Reading | Layer | Literal Stop (if `literal`) | Source Report |
|---|---|---|---|---|---|
| `UnitChainChild` | defect | `test262` | spec | `—` | `docs/spec-issues/36-islabelledfunction-labelleditem.md` |
| `StringValueReservedWord` | defect | `test262` | spec | `—` | `docs/spec-issues/32-stringvalue-reservedword.md` |
| `LookaheadSourceTokens` | defect | `test262` | parser | `—` | `docs/spec-issues/44-lookahead-source-tokens.md` |
| `HTMLCloseCommentToken` | defect | `test262` | parser | `none` | `docs/spec-issues/41-annexb-html-close-comment-token.md` |
| `AnnexBRegExpOrder` | defect | `test262` | parser | `—` | `docs/spec-issues/40-annexb-regexp-order-group-count.md` |
| `AnnexBGroupCount` | defect | `test262` | parser | `—` | `docs/spec-issues/40-annexb-regexp-order-group-count.md` |
| `AnnexBModifierEarlyErrors` | defect | `test262` | spec | `none` | `docs/spec-issues/26-annexb-modifiers-early-errors.md` |
| `CoveredNodeParent` | defect | `test262` | parser | `none` | `docs/spec-issues/46-covered-node-parent.md` |
| `NumberMultiplyZeroSign` | defect | `proposed` | spec | `—` | `docs/spec-issues/01-number-multiply-zero-sign.md` |
| `GatherAvailableAncestorsEmptyCycleRoot` | defect | `literal` | spec | `sec-gather-available-ancestors@1.a` | `docs/spec-issues/02-gather-available-ancestors-empty-cycle-root.md` |
| `BuiltinReturnCompletion` | defect | `test262` | spec | `—` | `docs/spec-issues/03-builtin-async-return-value.md` |
| `ExecuteModuleAsyncDisposeResources` | defect | `test262` | spec | `—` | `docs/spec-issues/04-execute-module-tla-dispose.md` |
| `ParseTextErrorObjects` | defect | `proposed` | spec | `—` | `docs/spec-issues/05-parsetext-error-objects.md` |
| `DoWaitSyncTimeout` | defect | `test262` | spec | `sec-addwaiter@2` | `docs/spec-issues/06-dowait-sync-timeout.md` |
| `AtomicsWaitAsyncTimeoutAssert` | defect | `literal` | spec | `sec-enqueueatomicswaitasynctimeoutjob@1.b.ii` | `docs/spec-issues/09-atomics-waitasync-timeout-assert.md` |
| `AtomicsWaitAsyncTimeoutNegativeDelay` | defect | `literal` | spec | `sec-enqueueatomicswaitasynctimeoutjob@4` | `docs/spec-issues/09-atomics-waitasync-timeout-assert.md` |
| `GetUTCEpochNanosecondsNaN` | defect | `literal` | spec | `sec-getutcepochnanoseconds@4` | `docs/spec-issues/10-utc-large-local-time.md` |
| `MakeDayFiniteTimeValue` | defect | `proposed` | spec | `—` | `docs/spec-issues/10-utc-large-local-time.md` |
| `GetMatchStringStartAfterEnd` | defect | `literal` | spec | `sec-getmatchstring@1[sec-regexpbuiltinexec]` | `docs/spec-issues/11-regexp-lastindex-inside-surrogate-pair.md` |
| `AsyncBlockStartAwaitResult` | defect | `test262` | spec | `sec-asyncblockstart@4` | `docs/spec-issues/12-asyncblockstart-await-result.md` |
| `PromiseJobAbruptCompletion` | defect | `literal` | spec | `sec-jobs@-[sec-newpromisereactionjob]` | `docs/spec-issues/13-promise-job-abrupt-completion.md` |
| `NativeFunctionInitialName` | defect | `literal` | spec | `none` | `docs/spec-issues/14-nativefunction-initialname.md` |
| `SyntheticModuleLinkResets` | defect | `literal` | spec | `none` | `docs/spec-issues/15-synthetic-module-link.md` |
| `CreateDynamicFunctionPrivateIdentifiers` | defect | `proposed` | spec | `—` | `docs/spec-issues/20-dynamic-function-private-identifiers.md` |
| `IdentityEscapeJoinControls` | proposal | `proposed` | parser | `—` | `docs/spec-issues/21-identityescape-zwnj-zwj.md` |
| `LonePropertyGeneralCategoryAssert` | defect | `test262` | spec | `sec-runtime-semantics-unicodematchpropertyvalue-p-v@2[sec-compiletocharset]` | `docs/spec-issues/24-lone-property-gc-assert.md` |
| `PropNameCoverInitializedName` | defect | `proposed` | spec | `—` | `docs/spec-issues/29-propname-coverinitializedname.md` |
| `AllocateSharedArrayBufferByteLengthStore` | defect | `test262` | spec | `—` | `docs/spec-issues/43-allocatesharedarraybuffer-byte-length.md` |
| `ContainsAwaitCover` | defect | `test262` | spec | `—` | `docs/spec-issues/35-contains-awaitexpression-cover.md` |
| `SplitCodeUnitStrings` | defect | `test262` | spec | `—` | `docs/spec-issues/37-split-code-units.md` |
| `OrdinarySetReceiverHasProperty` | defect | `proposed` | spec | `—` | `docs/spec-issues/38-ordinaryset-receiver-has-property.md` |
| `MustCoverEarlyErrorOrder` | defect | `test262` | spec | `—` | `docs/spec-issues/39-must-cover-other-rules.md` |
| `RacesNotBoth` | defect | `literal` | none | `none` | `docs/spec-issues/23-races-not-both.md` |
| `InitHappensBeforeOverlap` | defect | `literal` | none | `none` | `docs/spec-issues/48-init-overlap-equal-ranges.md` |
| `MemoryRangeSameBlock` | defect | `proposed` | none | `—` | `docs/spec-issues/50-memory-range-same-block.md` |
| `CreateIntrinsicsAsyncArgument` | defect | `test262` | spec | `sec-setfunctionname@5.a[sec-createbuiltinfunction]` | `docs/spec-issues/33-createintrinsics-async-argument-position.md` |
| `SortInfiniteComparator` | defect | `test262` | spec | `—` | `docs/spec-issues/31-sort-infinite-comparator.md` |
| `UnregisterIteratesCopy` | defect | `test262` | spec | `none` | `docs/spec-issues/45-unregister-iterates-cells.md` |
| `IsCharacterClassControlLetter` | defect | `test262` | spec | `—` | `docs/spec-issues/49-annexb-ischaracterclass-classcontrolletter.md` |
| `BigIntMaximumSize` | proposal | `proposed` | spec | `—` | `docs/spec-issues/51-bigint-maximum-size.md` |
| `StringLengthOverflow` | defect | `proposed` | spec | `—` | `docs/spec-issues/53-string-length-overflow.md` |
| `StringMaximumLength` | proposal | `proposed` | spec | `—` | `docs/spec-issues/54-string-maximum-length.md` |
| `RegExpUnicodeEscapeLookahead` | defect | `test262` | parser | `—` | `docs/spec-issues/55-regexp-unicode-escape-lookahead.md` |
| `PostASILexicalGoal` | defect | `test262` | parser | `—` | `docs/spec-issues/56-post-asi-lexical-goal.md` |
| `ForLexicalHeaderASI` | defect | `test262` | parser | `—` | `docs/spec-issues/57-asi-for-lexical-header.md` |
| `CoverMatchedVirtualSemis` | defect | `test262` | parser | `—` | `docs/spec-issues/58-cover-reparse-virtual-semicolons.md` |
| `RegExpExecEndOfString` | defect | `test262` | spec | `—` | `docs/spec-issues/59-regexp-exec-end-of-string.md` |
| `AnnexBFunctionEvalEmpty` | defect | `test262` | spec | `—` | `docs/spec-issues/60-annexb-function-eval-empty.md` |
| `AnnexBQuantifiableAssertion` | defect | `test262` | spec | `—` | `docs/spec-issues/61-annexb-quantifiable-assertion.md` |
| `AnnexBCapturingParensAssert` | defect | `test262` | spec | `—` | `docs/spec-issues/62-annexb-capturing-parens-assert.md` |
| `AnnexBReplacingAndB33` | defect | `test262` | spec | `—` | `docs/spec-issues/63-annexb-replacing-and-b33.md` |
| `SupplementalCoveredBy` | defect | `test262` | spec | `—` | `docs/spec-issues/64-supplemental-covered-by.md` |
| `ToISOStringYearForm` | defect | `test262` | spec | `—` | `docs/spec-issues/65-toisostring-year-form.md` |
| `ModuleDiamondCircularityAsserts` | defect | `test262` | spec | `—` | `docs/spec-issues/66-module-diamond-circularity-asserts.md` |
| `MemoryModelRMWCycleAndRbf` | defect | `proposed` | none | `—` | `docs/spec-issues/67-memory-model-rmw-cycle.md` |
| `WeakRefAllCellsAndSuspendWaiter` | defect | `proposed` | spec | `—` | `docs/spec-issues/68-weakref-cells-and-unicode-sorts.md` |

### Detailed Errata & Proposal Decisions (with Alternatives & Risks)

#### `UnitChainChild` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/36-islabelledfunction-labelleditem.md`
- **Rationale**: "the |X| of _n_" names a child of _n_ (§5.1.2 gives a node only its right-hand side's children), so IsLabelledFunction 1-2 never find the |LabelledStatement| under a |Statement| node: read by §5.1.2 alone, step 1 returns *false* for every |Statement| node and `if (1) l: function f() {}` is valid; test262's labelled-fn-stmt*.js require a SyntaxError. The model reads "_n_ is a |X|" through the unit chain (decisions.md, child-of-through-unit-chain), so its literal reading passes step 1 and stops (a sort error) at step 2, where _n_'s production has no |X|. The test262 and proposed reading: |X| is taken from the first node of _n_'s unit chain whose production has one.

#### `StringValueReservedWord` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/32-stringvalue-reservedword.md`
- **Rationale**: "the StringValue of any |ReservedWord| except for `yield` or `await`" takes the StringValue of a |ReservedWord|, for which StringValue has no row. The literal text stops there. The test262 and proposed reading: the StringValue of a terminal is the String value of its code points (test262's val-*-via-escape-*.js require a SyntaxError for an |IdentifierName| that spells a reserved word with escapes).

#### `LookaheadSourceTokens` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/44-lookahead-source-tokens.md`
- **Rationale**: A lookahead restriction reads "the immediately following input token sequence" (§5.1.6.7), and §12.10 inserts semicolons "into the source code token stream": the text does not say whether an inserted semicolon is a token a lookahead reads. Read as one, `if (0) let` LF `[a] = 0;` is a sentence. The literal text stops wherever a lookahead reads at an inserted semicolon. The test262 and proposed reading: a lookahead reads the source's tokens, past the semicolons §12.10 inserted (test262's let-array-with-newline.js require a SyntaxError).

#### `HTMLCloseCommentToken` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/41-annexb-html-close-comment-token.md`
- **Rationale**: B.1.1 adds |HTMLCloseComment| as an alternative of |InputElementHashbangOrRegExp| of its own, not under |Comment|, and §5.1.3 drops only white space and comments from the input elements: literally a first-line `-->` is a token that no syntactic production has, and the |Script| has no parse (a SyntaxError). The test262 and proposed reading: an |HTMLCloseComment| input element is a comment (test262's single-line-html-close-first-line-{1,2,3}.js).

#### `AnnexBRegExpOrder` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/40-annexb-regexp-order-group-count.md`
- **Rationale**: B.1.2's "each alternative is considered only if previous production alternatives do not match" says neither what an alternative matches nor how nested choices combine, and without an order its grammar is ambiguous (`/a{1}/`, `/\b*/`, `/\1/`). The literal text stops on a pattern with more than one parse. The test262 and proposed reading: commitment: a node of a nonterminal B.1.2 restates uses an alternative only if no earlier alternative of it derives any span from the node's start (tc39/ecma262 #2228; test262's annexB/built-ins/RegExp).

#### `AnnexBGroupCount` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/40-annexb-regexp-order-group-count.md`
- **Rationale**: B.1.2's condition on `AtomEscape :: DecimalEscape`, "the CapturingGroupNumber of |DecimalEscape| is ≤ CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)", reads the |Pattern| whose parse the condition itself decides. The literal text stops on a pattern with more than one parse. The test262 and proposed reading: stratified: the count is that of a committed parse of the input as Pattern[~UnicodeMode, ~UnicodeSetsMode, ~NamedCaptureGroups] with the condition true (test262's legacy-octal-escape.js).

#### `AnnexBModifierEarlyErrors` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/26-annexb-modifiers-early-errors.md`
- **Rationale**: §22.2.1.1's modifier rules are on |Atom|'s productions; under B.1.2's grammar `(?ii:a)` is an |ExtendedAtom|, for which B.1.2.1 adds no such rule, so literally `/(?ii:a)/`, `/(?-:a)/` and `/(?i-i:a)/` are valid patterns without the u or v flag on a B.1.2 host. The test262 and proposed reading: §22.2.1.1's rules of the two modifier productions of |Atom| apply to the |ExtendedAtom| productions with the same right-hand sides.

#### `CoveredNodeParent` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/46-covered-node-parent.md`
- **Rationale**: §5.1.5 reparses a cover with _n_ as goal, so the covered node roots a tree of its own: "contained within", "most closely contains" and "the parent of" (such as IsInTailPosition step 2) fail for a node inside it, and read literally `return (f(n - 1))` is not a tail call. The test262 and proposed reading: the covered node takes the cover's place in the tree, its parent being the cover's parent (test262's tco-pos.js; docs/spec-issues/46-covered-node-parent.md).

#### `NumberMultiplyZeroSign` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/01-number-multiply-zero-sign.md`
- **Rationale**: See `docs/spec-issues/01-number-multiply-zero-sign.md`.

#### `GatherAvailableAncestorsEmptyCycleRoot` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-gather-available-ancestors@1.a`, report=`docs/spec-issues/02-gather-available-ancestors-empty-cycle-root.md`
- **Rationale**: See `docs/spec-issues/02-gather-available-ancestors-empty-cycle-root.md`.

#### `BuiltinReturnCompletion` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/03-builtin-async-return-value.md`
- **Rationale**: See `docs/spec-issues/03-builtin-async-return-value.md`.

#### `ExecuteModuleAsyncDisposeResources` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/04-execute-module-tla-dispose.md`
- **Rationale**: See `docs/spec-issues/04-execute-module-tla-dispose.md`.

#### `ParseTextErrorObjects` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/05-parsetext-error-objects.md`
- **Rationale**: The pinned text says ParseText and ParsePattern return "a List of one or more *SyntaxError* objects" without specifying a Realm Record, and ten caller steps test "is a List of errors" where the sort "error" is never defined (tc39/ecma262 #3868). SpecTec bakes in three choices: @formal-parsetextin, @ph-syntax-errors and early-error rules allocate a singleton *SyntaxError* object in currentRealm; Engine/Host/Opts.lean pushes a realm execution context before top-level ParseScript/ParseModule; and @sort-error defines "error" as an Object with [[ErrorData]] (docs/spec-issues/05-parsetext-error-objects.md).

#### `DoWaitSyncTimeout` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-addwaiter@2`, report=`docs/spec-issues/06-dowait-sync-timeout.md`
- **Rationale**: See `docs/spec-issues/06-dowait-sync-timeout.md`.

#### `AtomicsWaitAsyncTimeoutAssert` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-enqueueatomicswaitasynctimeoutjob@1.b.ii`, report=`docs/spec-issues/09-atomics-waitasync-timeout-assert.md`
- **Rationale**: See `docs/spec-issues/09-atomics-waitasync-timeout-assert.md`.

#### `AtomicsWaitAsyncTimeoutNegativeDelay` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-enqueueatomicswaitasynctimeoutjob@4`, report=`docs/spec-issues/09-atomics-waitasync-timeout-assert.md`
- **Rationale**: _now_ is read after DoWait's reading from which [[TimeoutTime]] was computed, so the literal difference is negative when the clock has advanced past [[TimeoutTime]], and HostEnqueueTimeoutJob takes a non-negative finite Number. The proposed reading clamps the text's own difference at zero, so that _now_ + _delay_ is 𝔽([[TimeoutTime]]) whenever the delay is positive: the Job runs no earlier than that time value, which is what AtomicsWaitAsyncTimeoutAssert's proposed Assert needs. Clamping the exact difference instead (𝔽(max([[TimeoutTime]] - ℝ(_now_), 0))) can round the delay down across a millisecond that 𝔽([[TimeoutTime]]) rounds up to. While SpecTec keeps the literal subtraction at EnqueueAtomicsWaitAsyncTimeoutJob step 4, runtime parameter-sort checks are omitted and Engine.Host.Strategy.msCeil clamps negative timeout delays up to 0 ms (and wakeFinite in 16-host-laws-jobs.spectec caps finite agent suspension timeouts at maxTime = 8.64 × 10^15 ms).

#### `GetUTCEpochNanosecondsNaN` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-getutcepochnanoseconds@4`, report=`docs/spec-issues/10-utc-large-local-time.md`
- **Rationale**: Alongside keeping UTC step 1 literal here, SpecTec bakes in MakeDayFiniteTimeValue on MakeDay step 8 and omits runtime return-sort checks (so GetUTCEpochNanoseconds exceeding MinEpochNanoseconds..MaxEpochNanoseconds on large UTC(_t_) inputs does not stop with sortError; docs/spec-issues/10-utc-large-local-time.md).

#### `MakeDayFiniteTimeValue` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/10-utc-large-local-time.md`
- **Rationale**: §21.4.1.1 defines a finite time value first as an integral Number and then states a ±8.64 × 1015 ms range. On `Date.UTC(275761, 0, -256)`, 1 January 275761 exceeds 8.64 × 1015 ms while the resulting date is in range; SpecTec (@sec-makeday and @sort-time-value) bakes in reading "finite time value" as any finite integral Number, matching V8, SpiderMonkey and JavaScriptCore (docs/spec-issues/10-utc-large-local-time.md).

#### `GetMatchStringStartAfterEnd` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-getmatchstring@1[sec-regexpbuiltinexec]`, report=`docs/spec-issues/11-regexp-lastindex-inside-surrogate-pair.md`
- **Rationale**: While GetMatchString step 1's Assert is kept literal, @ph-input-index-of (Helpers.spectec) bakes in mapping a trailing-surrogate _lastIndex_ backward to the containing surrogate pair's code-point index at RegExpBuiltinExec step 13.b (and returning $ListLen(_input_) at _lastIndex_ = _length_, see RegExpExecEndOfString). Consequently /(?:)/gu stops at GetMatchString step 1 while /./gu at lastIndex = 1 on "\u{1F600}" returns the lone trailing surrogate "\uDE00" (docs/spec-issues/11-regexp-lastindex-inside-surrogate-pair.md).

#### `AsyncBlockStartAwaitResult` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-asyncblockstart@4`, report=`docs/spec-issues/12-asyncblockstart-await-result.md`
- **Rationale**: See `docs/spec-issues/12-asyncblockstart-await-result.md`.

#### `PromiseJobAbruptCompletion` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-jobs@-[sec-newpromisereactionjob]`, report=`docs/spec-issues/13-promise-job-abrupt-completion.md`
- **Rationale**: In addition to checking NewPromiseReactionJob's completion at the job boundary, SpecTec's host laws assign *null*-realm promise Jobs to the surrounding agent with per-agent FIFO order, and Engine.Host.prepareJobOn pushes an execution context for the agent's realm so species resolving functions have a running execution context (docs/spec-issues/13-promise-job-abrupt-completion.md).

#### `NativeFunctionInitialName` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/14-nativefunction-initialname.md`
- **Rationale**: The proposed text: "If _func_ is a built-in function object, return an implementation-defined String source code representation of _func_. The representation must have the syntax of a |NativeFunction|. Additionally, if _func_ has an [[InitialName]] internal slot, _func_.[[InitialName]] is a String, and _func_.[[InitialName]] is matched by |NativeFunctionAccessor?| |PropertyName|, the portion of the returned String that would be matched by |NativeFunctionAccessor?| |PropertyName| must be _func_.[[InitialName]]." Both requirements are NativeFunctionSource's law. While non-PropertyName [[InitialName]] strings such as "a b" have no conforming output and stop on residue when source text is unavailable, S20.spectec bakes in allowing an empty "" [[InitialName]] without a |PropertyName| Parse Node (for anonymous built-ins), and NativeFunctionSource restricts .ok representations to ASCII names (docs/spec-issues/14-nativefunction-initialname.md).

#### `SyntheticModuleLinkResets` (baked in: `literal` | defect | layer: spec)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/15-synthetic-module-link.md`
- **Rationale**: See `docs/spec-issues/15-synthetic-module-link.md`.

#### `CreateDynamicFunctionPrivateIdentifiers` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/20-dynamic-function-private-identifiers.md`
- **Rationale**: See `docs/spec-issues/20-dynamic-function-private-identifiers.md`.

#### `IdentityEscapeJoinControls` (baked in: `proposed` | proposal | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/21-identityescape-zwnj-zwj.md`
- **Rationale**: Since Unicode 15.1 added  (U+200C) and  (U+200D) to ID_Continue, `IdentityEscape[~UnicodeMode] :: SourceCharacter but not UnicodeIDContinue` makes `/\u200C/` and `/\u200D/` (with literal ZWNJ/ZWJ) SyntaxErrors outside §B.1.2 without an Annex F record. Because test262's S7.8.5_A1.4_T2.js permits SyntaxError for ID_Continue characters, this is a proposed normative restoration rather than a test262 requirement (docs/spec-issues/21-identityescape-zwnj-zwj.md).

#### `LonePropertyGeneralCategoryAssert` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-runtime-semantics-unicodematchpropertyvalue-p-v@2[sec-compiletocharset]`, report=`docs/spec-issues/24-lone-property-gc-assert.md`
- **Rationale**: See `docs/spec-issues/24-lone-property-gc-assert.md`.

#### `PropNameCoverInitializedName` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/29-propname-coverinitializedname.md`
- **Rationale**: ObjectLiteral's duplicate-`__proto__` early-error rule calls PropertyNameList -> PropName on every PropertyDefinition, including CoverInitializedName (`({a = 1})`), which has no PropName row in §8.6.5. SpecTec bakes in @row-propname-coverinitializedname, @formal-protopropertycount, and bottom-up child early-error short-circuiting so evaluation never stops with sortError (docs/spec-issues/29-propname-coverinitializedname.md).

#### `AllocateSharedArrayBufferByteLengthStore` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/43-allocatesharedarraybuffer-byte-length.md`
- **Rationale**: SetValueInBuffer takes an ArrayBuffer or SharedArrayBuffer (its step 4 reads [[ArrayBufferData]]); _byteLengthBlock_ is a Shared Data Block, which ArrayBufferByteLength and SharedArrayBuffer.prototype.grow read with GetRawBytesFromSharedBlock. The reading writes it as SetValueInBuffer's shared branch would (IsNoTearConfiguration(~biguint64~, ~seq-cst~) is *true*). test262 constructs growable SharedArrayBuffers (built-ins/SharedArrayBuffer/prototype/grow).

#### `ContainsAwaitCover` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/35-contains-awaitexpression-cover.md`
- **Rationale**: An `await` expression parses as UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead, and |AwaitExpression| is only the cover's refined interpretation, so the default definition never meets an |AwaitExpression| and every early error rule "X Contains |AwaitExpression|" holds vacuously. test262 requires them (built-ins/AsyncGeneratorFunction/instance-await-expr-in-param.js, language/expressions/async-generator/early-errors-expression-formals-contains-await-expr.js, language/expressions/async-arrow-function/await-as-param-nested-arrow-body-position.js). The reading counts the cover of that production, and not the cover of an |AwaitUsingDeclaration|, as an |AwaitExpression|. The proposed text is the equivalent Contains row for UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead: "1. If _symbol_ is |AwaitExpression|, return *true*. 2. Let _expr_ be the |AwaitExpression| that is covered by |CoverAwaitExpressionAndAwaitUsingDeclarationHead|. 3. Return _expr_ Contains _symbol_."

#### `SplitCodeUnitStrings` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/37-split-code-units.md`
- **Rationale**: The literal step passes a List of code units to CreateArrayFromList, whose parameter is a List of ECMAScript language values; a code unit is not one. test262 requires the Array's elements to be the Strings of one code unit each (built-ins/String/prototype/split/separator-empty-string-instance-is-string.js), as the method's description says: "any _separator_ coerced to the empty String splits the *this* value into individual code units".

#### `OrdinarySetReceiverHasProperty` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/38-ordinaryset-receiver-has-property.md`
- **Rationale**: Step 2.d.i's Assert follows `_receiver_.[[GetOwnProperty]](_propertyKey_)` returning *undefined*, which fails both when a Proxy receiver's trap hides a configurable target property and when an ordinary `_receiver_` inherits `_propertyKey_` from its prototype. SpecTec silences step 2.d.i via `assert pass` in S10.spectec:190 (docs/spec-issues/38-ordinaryset-receiver-has-property.md).

#### `MustCoverEarlyErrorOrder` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/39-must-cover-other-rules.md`
- **Rationale**: When a cover fails its "must cover" rule (`([...x = []]) => {}`, `async (...x = []) => {}`), unordered sibling and ancestor early-error rules still ask for "the |n| that is covered by _p_" — a Parse Node that does not exist. SpecTec (@formal-earlyerrorsof and LinEarly.linOwn) short-circuits children before parents and runs `must_cover` rules before other rules at each node (docs/spec-issues/39-must-cover-other-rules.md).

#### `RacesNotBoth` (baked in: `literal` | defect | layer: none)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/23-races-not-both.md`
- **Rationale**: Step 1.a of Races (sec-races) is always true: an execution's happens-before is a strict partial order, so _eventA_ and _eventB_ never both happen-before each other, and any two conflicting events race. The memory model's meaning (Ecma.MemoryModel.Race) reads the literal text. The proposed text of step 1.a: "If neither _eventA_ happens-before _eventB_ in _execution_ nor _eventB_ happens-before _eventA_ in _execution_, then".

#### `InitHappensBeforeOverlap` (baked in: `literal` | defect | layer: none)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/48-init-overlap-equal-ranges.md`
- **Rationale**: The third condition of happens-before orders an ~init~ write only before events whose memory ranges are *overlapping*, and "overlapping" excludes equal ranges, so a 1-byte event at an ~init~ event's byte is not ordered after it. The proposed text: "SharedDataBlockEventSet(_execution_) contains both _eventA_ and _eventB_, _eventA_.[[Order]] is ~init~, _eventA_ and _eventB_ are not the same Shared Data Block event, and _eventA_ and _eventB_ do not have disjoint memory ranges."

#### `MemoryRangeSameBlock` (baked in: `proposed` | defect | layer: none)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/50-memory-range-same-block.md`
- **Rationale**: A memory range is a Set of integers, the byte indices from [[ByteIndex]], with no [[Block]] in it, so reads-bytes-from's "has _readEvent_.[[ByteIndex]] + _i_ in its memory range" and coherent reads' "has _byteLocation_ in its memory range" (step 1.c.ii) admit a write to another Shared Data Block at the same index. The proposed text, which the memory model's meaning (Ecma.MemoryModel.Rbf.Valid, CoherentReads) reads: "Each event _writeEvent_ with index _i_ in _writes_ has _readEvent_.[[Block]] as its [[Block]] and _readEvent_.[[ByteIndex]] + _i_ in its memory range", and in step 1.c.ii "a WriteSharedMemory or ReadModifyWriteSharedMemory event _value_ whose [[Block]] is _readEvent_.[[Block]] and that has _byteLocation_ in its memory range".

#### `CreateIntrinsicsAsyncArgument` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`sec-setfunctionname@5.a[sec-createbuiltinfunction]`, report=`docs/spec-issues/33-createintrinsics-async-argument-position.md`
- **Rationale**: Step 2 creates each built-in function by "CreateBuiltinFunction(_steps_, _length_, _name_, _slots_, _realmRecord_, _proto_, _async_)", which passes _async_ as CreateBuiltinFunction's _prefix_ and gives no accessor its prefix; read literally, SetFunctionName concatenates a Boolean and realm creation stops. test262 requires both: built-ins/Array/fromAsync/ (an async function) and built-ins/Map/prototype/size/name.js (*"get size"*). The proposed text: "CreateBuiltinFunction(_steps_, _length_, _name_, _slots_, _realmRecord_, _proto_, _prefix_, _async_), where _prefix_ is *"get"* or *"set"* for a get or set accessor function of a built-in property and ~empty~ otherwise", with an ~empty~ _prefix_ read as not present.

#### `SortInfiniteComparator` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/31-sort-infinite-comparator.md`
- **Rationale**: The definition of a consistent comparator reads each result as ℝ(_comparator_(_a_, _b_)), which has no value for ±∞; the literal reading stops there. No test262 test has a comparator return ±∞. The test262 reading has no ℝ step: by SortStep's law no consistent comparator gives a ±∞ result, so the order is the host's, and both test hosts order by the result's sign. The proposed text compares the Number itself with *+0*𝔽 where the text takes ℝ of it, in the sort order's two conditions ("if _sortCompare_(old[_j_], old[_k_]) &lt; *+0*𝔽", "… = *+0*𝔽") and in the definition of a consistent comparator ("_a_ &lt;C _b_ means _comparator_(_a_, _b_) &lt; *+0*𝔽", likewise for =C and &gt;C).

#### `UnregisterIteratesCopy` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`none`, report=`docs/spec-issues/45-unregister-iterates-cells.md`
- **Rationale**: The literal step removes from the List it iterates, and the For each convention does not say which element comes next; read literally, the cell after a removed one is skipped. test262 requires every cell with the token to go (built-ins/FinalizationRegistry/prototype/unregister/unregister-object-token.js and unregister-symbol-token.js register two cells with one token in a row). The proposed text iterates a copy, as above.

#### `IsCharacterClassControlLetter` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/49-annexb-ischaracterclass-classcontrolletter.md`
- **Rationale**: IsCharacterClass has no definition for this production of §B.1.2, whose CharacterValue §B.1.2.4 gives, and §B.1.2.1's range rules ask for it of every |ClassAtom| of a range: `/[\c1-\c5]/`. The literal text stops there (it asks IsCharacterClass of |ClassControlLetter|, which has no definition either). The row is the twin of ClassEscape :: CharacterEscape's: the escape is one character. No test262 test has `\c` and a digit or `_` at a range's end; annexB/language/literals/regexp/class-escape.js reads `[\c1]` as U+0011.

#### `BigIntMaximumSize` (baked in: `proposed` | proposal | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/51-bigint-maximum-size.md`
- **Rationale**: §6.1.6.2 says a BigInt "may be any size and is not limited to a particular bit-width", and BigInt::exponentiate, BigInt::leftShift, BigInt::multiply, BigInt::add, BigInt::subtract and BigInt.asUintN return their exact results whatever their size; every implementation has a maximum size and throws a *RangeError* past it (V8 at 230 bits). SpecTec checks BigIntTooLarge before forming the result (propagating `?` through binary operators, BigInt::signedRightShift, and `++`/`--`; docs/spec-issues/51-bigint-maximum-size.md).

#### `StringLengthOverflow` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/53-string-length-overflow.md`
- **Rationale**: §6.1.4 defines the String type as sequences of up to 253 - 1 16-bit elements, yet String.prototype.repeat (`"ab".repeat(2 ** 52)`), String.prototype.concat, `+`, and JoinIndexedProperties have no `> 2^53 - 1` length guard before forming their result. SpecTec checks StringTooLarge (`Host.ValueLaws.stringTooLarge`, answering *true* past 228 and therefore past 253 - 1 in Engine) and throws a *RangeError* (docs/spec-issues/53-string-length-overflow.md).

#### `StringMaximumLength` (baked in: `proposed` | proposal | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/54-string-maximum-length.md`
- **Rationale**: Even below §6.1.4's 253 - 1 ceiling, every engine enforces a smaller finite-memory maximum String length and throws a *RangeError* past it (V8 228 on 32-bit and 229 - 24 on 64-bit, SpiderMonkey 230 - 2, JavaScriptCore 231 - 1). SpecTec asks the host via StringTooLarge (answering *true* past 228 code units in Engine) and throws a *RangeError* (docs/spec-issues/54-string-maximum-length.md).

#### `RegExpUnicodeEscapeLookahead` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/55-regexp-unicode-escape-lookahead.md`
- **Rationale**: In §22.2.1's formal grammar, RegExpUnicodeEscapeSequence[+UnicodeMode] has both `u HexLeadSurrogate \u HexTrailSurrogate` and unguarded `u HexLeadSurrogate` alongside `u HexTrailSurrogate`, leaving `/\uD800\uDC00+/u`, `/[\uD800\uDC00]/u` and `/(?a)/` context-free ambiguous. SpecTec attaches a 16-prefix `[lookahead not_in { "\uDC", … }]` override in grammar-meta.txt and 04-grammar-regexp.spectec so greedy surrogate pairing is unambiguous and ParseLaws.complete holds (docs/spec-issues/55-regexp-unicode-escape-lookahead.md).

#### `PostASILexicalGoal` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/56-post-asi-lexical-goal.md`
- **Rationale**: Before ASI inserts `;` after `let a` or `do {} while (false)`, no |RegularExpressionLiteral| is syntactically permitted, so literal §12 scans `/` on the next line as `DivPunctuator` and never re-lexes it after inserting `;` — rejecting `let a\n/x/.test("x")`! §12 also omits initial lexical goals for non-Script/Module ParseText calls. SpecTec (GoalsAt and NextASI in 04-derives.spectec) probes offending tokens under InputElementDiv and re-scans post-ASI tokens under their post-`;` syntactic context, using InputElementHashbangOrRegExp only at index 0 of |Script| or |Module| (docs/spec-issues/56-post-asi-lexical-goal.md).

#### `ForLexicalHeaderASI` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/57-asi-for-lexical-header.md`
- **Rationale**: In `ForStatement : for ( LexicalDeclaration Expression? ; Expression? ) Statement`, the first header `;` belongs to the child |LexicalDeclaration| rather than |ForStatement|; §5.1.5's declarative ASI also leaves `a = b\n+c` ambiguous; and §5.1.6.7 leaves `[no LineTerminator here]` inside lookahead sets undefined. SpecTec (04-derives.spectec) bans virtual `;` at the end of a `for`-header LexicalDeclaration (`ForHeadersExplicit`), formalizes left-to-right maximal viable prefix ASI (`ValidASI`), and adds `LookItem.noLT` (docs/spec-issues/57-asi-for-lexical-header.md).

#### `CoverMatchedVirtualSemis` (baked in: `test262` | defect | layer: parser)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/58-cover-reparse-virtual-semicolons.md`
- **Rationale**: §5.1.5 and §12.10 define ASI only for |Script| and |Module|, without stating that virtual semicolons inserted inside a cover _p_ (such as `(function () { let a\n return 1 })()`) survive when _p_ is reparsed as _n_. SpecTec's GrammarCtx.CoverIs (06-node-rel.spectec) and Ecma.reparse (Ops/Leaf.lean, Relabel.lean) preserve virtual semicolons inside reparsed covers (docs/spec-issues/58-cover-reparse-virtual-semicolons.md).

#### `RegExpExecEndOfString` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/59-regexp-exec-end-of-string.md`
- **Rationale**: Step 13.a exits only when `_lastIndex_ > _length_`, so at `_lastIndex_ = _length_` (reached on `""`, `/$/`, and the exhaustion step of every `/g` match) step 13.b asks for non-existent `element _lastIndex_ of _string_` in both BMP and Unicode modes. SpecTec's `@ph-input-index-of` (Helpers.spectec:78-89) returns `$ListLen(_input_)` when `_lastIndex_ == _length_` (docs/spec-issues/59-regexp-exec-end-of-string.md).

#### `AnnexBFunctionEvalEmpty` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/60-annexb-function-eval-empty.md`
- **Rationale**: All three Annex B.3.2 replacement algorithms (`FunctionDeclarationInstantiation`, `GlobalDeclarationInstantiation`, `EvalDeclarationInstantiation`) run in place of |FunctionDeclaration| Evaluation and end with `Return ~unused~` instead of `Return ~empty~`, which would leak `~unused~` out of `eval("{ function f() {} }")` and overwrite prior statement values. SpecTec (S15.spectec:831-837) discards the closure's normal `~unused~` result and returns `~empty~` (docs/spec-issues/60-annexb-function-eval-empty.md).

#### `AnnexBQuantifiableAssertion` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/61-annexb-quantifiable-assertion.md`
- **Rationale**: Substituting |QuantifiableAssertion| for |Atom| in `Term :: Atom Quantifier` calls 2-argument `CompileAtom(_regexpRecord_, _direction_)`, which has no row for |QuantifiableAssertion| (whose semantics in §B.1.2.6 is 1-argument `CompileAssertion(_regexpRecord_)`). SpecTec adds `@row-compilesubpattern-quantifiableassertion-quantifier` in Helpers.spectec calling 1-argument `CompileAssertion` (docs/spec-issues/61-annexb-quantifiable-assertion.md).

#### `AnnexBCapturingParensAssert` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/62-annexb-capturing-parens-assert.md`
- **Rationale**: §B.1.2.2 extends step 2 of CountLeftCapturingParensWithin to count `ExtendedAtom` groups, but leaves step 1 asserting `#sec-patterns`, which fails on every quantified §B.1.2 `ExtendedAtom` or `QuantifiableAssertion` (`#sec-regular-expressions-patterns`). SpecTec includes all 36 Annex B RegExp productions in `clause_prods @sec-patterns` (00-decls.spectec) and dispatches ParsePattern and CompileToCharSet under §B.1.2 (docs/spec-issues/62-annexb-capturing-parens-assert.md).

#### `AnnexBReplacingAndB33` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/63-annexb-replacing-and-b33.md`
- **Rationale**: §B.3.2 tests "Early Errors for _func_" on a Function Object `_func_` and "_code_ Contains _x_" on a Parse Node `_x_`; §B.3.3 speaks of a "synthetic |BlockStatement|" with no AST or SDO rules; and §B.1.1 extends MultiLineComment with optional `HTMLCloseComment?`, making `/*a\nb*/` ambiguous. SpecTec reparses spliced `"var " + F + ";"` on the root source, widens Contains to Parse Node identity, splices `{` `}` for B.3.3 via `$CoveredBy(|IfStatement|, node)` (including in `LinEarly.linTree`), and existentially quantifies trivia trees (docs/spec-issues/63-annexb-replacing-and-b33.md).

#### `SupplementalCoveredBy` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/64-supplemental-covered-by.md`
- **Rationale**: CallMemberExpression and AwaitExpression use "covered by" with no "must cover" rule anywhere in ECMA-262, and Keyed/IteratorDestructuringAssignmentEvaluation ask for the |AssignmentPattern| covered by |DestructuringAssignmentTarget| whereas §13.15.5 puts the "must cover" rule on its child |LeftHandSideExpression|. SpecTec's `$CoveredBy` (`Ecma.reparse` in Ops/Leaf.lean) reparses on demand whenever `(n, k)` was not cached by `must_cover` (docs/spec-issues/64-supplemental-covered-by.md).

#### `ToISOStringYearForm` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/65-toisostring-year-form.md`
- **Rationale**: §21.4.1.32 permits both 4-digit `YYYY` and expanded `+00YYYY` for years in `0..9999`, whereas test262 and all engines require 4-digit `YYYY` for `0..9999`. SpecTec adds `$ExpandedYearForm` in S21.spectec and binds it to `false` in Engine/Host/Core.lean (docs/spec-issues/65-toisostring-year-form.md).

#### `ModuleDiamondCircularityAsserts` (baked in: `test262` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/66-module-diamond-circularity-asserts.md`
- **Rationale**: Both algorithms pass a single mutable List (`_exportStarSet_` / `_resolveSet_`) across sibling `export *` branches without popping or copying, so any cycle-free diamond `export *` DAG (`a -> {b, c} -> d`) falsifies both circularity Asserts. SpecTec silences both via `assert pass` in S16.spectec:528, 563 (docs/spec-issues/66-module-diamond-circularity-asserts.md).

#### `MemoryModelRMWCycleAndRbf` (baked in: `proposed` | defect | layer: none)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/67-memory-model-rmw-cycle.md`
- **Rationale**: Unequal overlapping RMWs (`[0,2)` and `[0,4)`) are not ordered by §29.6.5 synchronizes-with (which requires equal ranges), allowing a 2-cycle in reads-bytes-from where ValueOfReadEvent ↔ ComposeWriteEventBytes diverges infinitely; §29.7.5 also leaves reads-bytes-from unquantified (since PR #3321), and §29.5.3 HostEventSet includes Synchronize events against §29.6.4. SpecTec (07-memory-model.spectec) defines ValueOf/Compose as an inductive least fixpoint, existentially quantifies `rbf`, converts Tear Free Reads' Assert to a conjunct, and defines HostSync over `inHost` (docs/spec-issues/67-memory-model-rmw-cycle.md).

#### `WeakRefAllCellsAndSuspendWaiter` (baked in: `proposed` | defect | layer: spec)
- **Literal stop / Report**: stop=`—`, report=`docs/spec-issues/68-weakref-cells-and-unicode-sorts.md`
- **Rationale**: SpecTec bakes in four prose/signature fixes: Cell.Emptied (25-host-laws-changes.spectec) empties *all* matching FinalizationRegistry cells rather than step 1.b's single `_cell_` per registry; $SuspendAgentUntil matches NotifyWaiter's Waiter Record parameter rather than `_thisAgent_` (#3328); $CanonicalPropertyValue selects UCD PropertyValueAliases.txt field 3 instead of a nonexistent "Canonical property value" column; and 00-decls.spectec declares `super [#"Module Record"]` on `#"Synthetic Module Record"` and models Private Name's `[[Description]]` as a Record field (docs/spec-issues/68-weakref-cells-and-unicode-sorts.md).

## 2. Grammar Readings, Rule Patches & Parser-Layer Choices
### Active `<emu-rule-reading>` entries baked into `01..07-grammar-*.spectec`
- **readings.emu — `sec-patterns` :: `IdentityEscape`** (pinned source hash `720c17925783...`): IdentityEscape[UnicodeMode] :: [+UnicodeMode] SyntaxCharacter [+UnicodeMode] `/` [~UnicodeMode] SourceCharacter but not UnicodeIDContinue [~UnicodeMode] `&#x200C;` [~UnicodeMode] `&#x200D;`
- **syntax.emu — `sec-patterns` :: `RegExpUnicodeEscapeSequence`** (pinned source hash `16035025e4c9...`): RegExpUnicodeEscapeSequence[UnicodeMode] :: [+UnicodeMode] `u` HexLeadSurrogate `\u` HexTrailSurrogate [+UnicodeMode] `u` HexLeadSurrogate [lookahead &notin; { `\uDC`, `\uDc`, `\udC`, `\udc`, `\uDD`, `\uDd`, `\udD`, `\udd`, `\uDE`, `\uDe`, `\udE`, `\ude`, `\uDF`, `\uDf`, `\udF`, `\udf` }] [+UnicodeMode] `u` HexTrailSurrogate [+UnicodeMode] `u` HexNonSurrogate [~UnicodeMode] `u` Hex4Digits [+UnicodeMode] `u{` CodePoint `}`The paragraph after the definition associates each `\u` |HexTrailSurrogate| whose lead is ambiguous with the nearest `u` |HexLeadSurrogate| that would otherwise have none: the one just before it, so that an escaped pair is one escape. The lone lead's lookahead says so: it is not followed by `\u` and two hex digits that begin a |HexTrailSurrogate|. Where such a prefix is not followed by two more hex digits, the pattern has no parse under either form: in a context with a `u` |HexLeadSurrogate|, `\u` begins only a |RegExpUnicodeEscapeSequence|.
  - *Notes on ID preservation*: `IdentityEscape[UnicodeMode]` replaces the first 3 alternatives under existing `ProdId`s and appends `ZWNJ` / `ZWJ` as fresh `ProdId`s at the end of `spec/ids/prod-ids.txt`. `RegExpUnicodeEscapeSequence` updates alternative 2's lookahead exclusion list in-place preserving its `ProdId`.
### Active `<emu-step-patch>` & `<emu-orphan-row>` entries
- **annexb.emu — clause `sec-parsepattern` alg `0`** (nest `—`): `1. [normative-optional] If the host is a web browser or otherwise supports , return ParsePatternAnnexB(_patternText_, _u_, _v_).`
- **annexb.emu — clause `sec-compiletocharset` alg `2`** (nest `sec-compiletocharset-annexb 0`): `1. [normative-optional] If the host is a web browser or otherwise supports , then`
- **annexb.emu — clause `sec-compiletocharset` alg `4`** (nest `sec-compiletocharset-annexb 1`): `1. [normative-optional] If the host is a web browser or otherwise supports , then`
- **syntax.emu — clause `sec-function-definitions-runtime-semantics-evaluation` alg `0`** (nest `—`): `1. Let _steps_ be EvaluationStepsOf(this Parse Node). 1. If _steps_ is not ~empty~, then 1. Let _result_ be _steps_(). 1. If _result_ is an abrupt completion, return _result_.`
- **Orphan SDO row (readings.emu) — clause `sec-static-semantics-mv` grammar `DecimalIntegerLiteral :: `0``**: 

### Parser-Level Errata Baked In (`test262` reading in `Ecma/Ops/Leaf.lean` & `Engine/Model/Leaf.lean`)
- `LookaheadSourceTokens`, `HTMLCloseCommentToken`, `AnnexBRegExpOrder`, `AnnexBGroupCount`, `CoveredNodeParent`: previously gated behind runtime `LitFlags`; in SpecTec the `test262` reading is unconditional (no `ErratumId` flags remain at runtime).
- `UnitChainChild`: child navigation through single-RHS unit chains unconditionally resolves the underlying child node rather than switching dynamically.

## 3. Baked-in Prose-Step Formalizations
A total of **285** `<emu-reading>` overlays existed across `spec/formal/*.emu`. Non-erratum prose formalizations (`definition` readings and single-interpretation `.emu-reading` blocks) were spliced directly into the SpecTec clause steps, eliminating SHA-256 hash guards and `Expr.prose` / `Ins.readings` nodes.


### `agents.emu` (8 reading entries)
- `sec-suspendthisagent` @ `7`: `definition`: 1. Perform LeaveCriticalSection(_waiterList_). 1. Perform SuspendAgentUntil(_waiterList_, _waiterRecord_.[[TimeoutTime]]). 1. Repeat, while 
- `sec-notifywaiter` @ `2.a`: `definition`: 1. Perform WakeAgent(_waiterRecord_.[[AgentSignifier]]).
- `sec-entercriticalsection` @ `1`: `definition`: 1. Assert: EnteredCriticalSections() is empty.
- `sec-getwaiterlist` @ `2`: `definition`: 1. Return WaiterListFor(_block_, _i_).
- `sec-entercriticalsection` @ `2`: `definition`: 1. Perform AcquireCriticalSection(_waiterList_).
- `sec-entercriticalsection` @ `3.g`: `definition`: 1. Append « _waiterList_.[[MostRecentLeaveEvent]], _enterEvent_ » to _eventsRecord_.[[AgentSynchronizesWith]].
- `sec-leavecriticalsection` @ `8`: `definition`: 1. Perform ReleaseCriticalSection(_waiterList_).
- `sec-createbytedatablock` @ `3`: `definition`: 1. Perform SetAllBytes(_dataBlock_, 0).

### `annexb.emu` (20 reading entries)
- `sec-compilesubpattern`: `default`: 1. Let _m_ be CompileAssertion of |QuantifiableAssertion| with argument _regexpRecord_. 1. Let _q_ be CompileQuantifier of |Quantifier|. 1. 
- `sec-compilesubpattern`: `default`: 1. Let _m_ be CompileAtom of |ExtendedAtom| with arguments _regexpRecord_ and _direction_. 1. Let _q_ be CompileQuantifier of |Quantifier|. 
- `sec-compilesubpattern`: `default`: 1. Return CompileAtom of |ExtendedAtom| with arguments _regexpRecord_ and _direction_.
- `sec-compileassertion`: `default`: 1. Let _m_ be CompileSubpattern of |Disjunction| with arguments _regexpRecord_ and ~forward~. 1. Return a new Matcher with parameters (_matc
- `sec-compileassertion`: `default`: 1. Let _m_ be CompileSubpattern of |Disjunction| with arguments _regexpRecord_ and ~forward~. 1. Return a new Matcher with parameters (_matc
- `sec-compileatom`: `default`: 1. Let _charSet_ be AllCharacters(_regexpRecord_). 1. If _regexpRecord_.[[DotAll]] is not *true*, then 1. Set _charSet_ to the CharSet conta
- `sec-compileatom`: `default`: 1. Let _cc_ be CompileCharacterClass of |CharacterClass| with argument _regexpRecord_. 1. Let _cs_ be _cc_.[[CharSet]]. 1. If _regexpRecord_
- `sec-compileatom`: `default`: 1. Let _m_ be CompileSubpattern of |Disjunction| with arguments _regexpRecord_ and _direction_. 1. Let _parenIndex_ be CountLeftCapturingPar
- `sec-compileatom`: `default`: 1. Let _addModifiers_ be the source text matched by |RegularExpressionModifiers|. 1. Let _removeModifiers_ be the empty String. 1. Let _modi
- `sec-compileatom`: `default`: 1. Let _addModifiers_ be the source text matched by the first |RegularExpressionModifiers|. 1. Let _removeModifiers_ be the source text matc
- `sec-countleftcapturingparenswithin` @ `2`: `definition`: 1. Let _atoms_ be the number of Parse Nodes contained within _parseNode_. 1. Let _extendedAtoms_ be the number of Parse Nodes contained with
- `sec-countleftcapturingparensbefore` @ `3`: `definition`: 1. Let _atoms_ be the number of Parse Nodes contained within _pattern_ that either occur before _parseNode_ or contain _parseNode_. 1. Let _
- `sec-if-statement-runtime-semantics-evaluation`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return ? Evaluation of _ifStatement_.
- `sec-static-semantics-hascallintailposition`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return HasCallInTailPosition of _ifStatement_ with argument
- `sec-static-semantics-vardeclarednames`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return the VarDeclaredNames of _ifStatement_.
- `sec-static-semantics-varscopeddeclarations`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return the VarScopedDeclarations of _ifStatement_.
- `sec-static-semantics-containsduplicatelabels`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return ContainsDuplicateLabels of _ifStatement_ with argume
- `sec-static-semantics-containsundefinedbreaktarget`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return ContainsUndefinedBreakTarget of _ifStatement_ with a
- `sec-static-semantics-containsundefinedcontinuetarget`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return ContainsUndefinedContinueTarget of _ifStatement_ wit
- `sec-static-semantics-contains`: `default`: 1. Let _ifStatement_ be the |IfStatement| that |IfStatement| is processed as. 1. Return _ifStatement_ Contains _symbol_.

### `asserts.emu` (14 reading entries)
- `sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset` @ `8.h.vii.1`: `definition`: 1. Assert: the number of elements in the BoundNames of _lhs_ is 1.
- `sec-runtime-semantics-scriptevaluation` @ `15`: `definition`: 1. Assert: it is not the case that the execution context stack is empty.
- `sec-generatorstart` @ `4.e`: `definition`: 1. Assert: _result_ is either a normal completion, a return completion, or a throw completion.
- `sec-asyncgeneratorstart` @ `4.e`: `definition`: 1. Assert: _result_ is either a normal completion, a return completion, or a throw completion.
- `sec-asyncblockstart` @ `1.d`: `definition`: 1. Assert: _result_ is either a normal completion, a return completion, or a throw completion.
- `sec-ordinarycallbindthis` @ `8`: `definition`: 1. Assert: _localEnv_.[[ThisBindingStatus]] is not ~initialized~.
- `sec-getexportednames` @ `6.a`: `definition`: 1. Assert: _module_.[[LocalExportEntries]] contains _exportEntry_.
- `sec-getexportednames` @ `7.a`: `definition`: 1. Assert: _module_.[[IndirectExportEntries]] contains _exportEntry_.
- `sec-resolveexport` @ `5.a.i`: `definition`: 1. Assert: _module_.[[LocalExportEntries]] contains _exportEntry_.
- `sec-resolveexport` @ `6.a.iii.1`: `definition`: 1. Assert: _module_.[[LocalExportEntries]] does not contain _exportEntry_.
- `sec-resolveexport` @ `6.a.iv`: `definition`: 1. Assert: _module_.[[IndirectExportEntries]] contains _exportEntry_.
- `sec-ParseJSON` @ `8`: `definition`: 1. If _result_ is an Object, then 1. Assert: _script_ Contains |ArrayLiteral| or _script_ Contains |ObjectLiteral|. 1. Else, 1. Assert: _res
- `sec-runsuspendedcontext` @ `5`: `definition`: 1. Assert: OnContextStack(_context_) is *false* and _callerContext_ is the running execution context.
- `sec-source-text-module-record-execute-module` @ `1`: `definition`: 1. Assert: _module_.[[Status]] is one of ~linked~, ~evaluating~, ~evaluating-async~, or ~evaluated~, and _module_.[[Environment]] is not ~em

### `charsets.emu` (29 reading entries)
- `sec-runtime-semantics-canonicalize-ch` @ `1.a`: `definition`: 1. Let _folded_ be SimpleCaseFold(_char_). 1. If _folded_ is not ~empty~, return _folded_.
- `sec-runtime-semantics-canonicalize-ch` @ `5`: `definition`: 1. Let _mappedCodePoints_ be toUppercase(« _codePoint_ »).
- `sec-allcharacters` @ `1.a`: `definition`: 1. Return CharSetNoScf().
- `sec-compileatom` @ `2.a`: `definition`: 1. Set _charSet_ to the CharSet containing the CharSetElements of _charSet_ which are not also CharSetElements of RightHandSideCharacters(« 
- `sec-compiletocharset` @ `1`: `definition`: 1. Return RightHandSideCharacters(« |WhiteSpace|, |LineTerminator| »).
- `sec-backreference-matcher` @ `1.q`: `definition`: 1. For each integer _i_ such that 0 ≤ _i_ &lt; _length_, in ascending order, do 1. If Canonicalize(_regexpRecord_, _input_[_rs_ + _i_]) is n
- `sec-runtime-semantics-charactersetmatcher-abstract-operation` @ `2.l`: `definition`: 1. Let _found_ be CharSetHasCanonical(_charSet_, _cc_, HasEitherUnicodeFlag(_regexpRecord_), _regexpRecord_.[[IgnoreCase]]).
- `sec-wordcharacters` @ `2`: `definition`: 1. If _regexpRecord_.[[IgnoreCase]] is *true*, let _extraWordChars_ be CharSetCanonExtra(_basicWordChars_, HasEitherUnicodeFlag(_regexpRecor
- `sec-regexp.escape` @ `4.a.iv`: `definition`: 1. Assert: the length of _hex_ is 2.
- `sec-regexpbuiltinexec` @ `21`: `definition`: 1. Assert: ℝ(OrdinaryGetOwnProperty(_array_, *"length"*).[[Value]]) = _capturingGroupsCount_ + 1.
- `sec-runtime-semantics-canonicalize-ch` @ `3`: `definition`: 1. Assert: _char_ is a code unit.
- `sec-runtime-semantics-canonicalize-ch` @ `7`: `definition`: 1. Assert: the number of elements in _mappedCodePoints_ is 1.
- `sec-runtime-semantics-characterrange-abstract-operation` @ `1`: `definition`: 1. Assert: the number of elements in _charSet_ is 1. 1. Assert: the sole element of _charSet_ is not a List or the number of elements in the
- `sec-wordcharacters` @ `3`: `definition`: 1. If HasEitherUnicodeFlag(_regexpRecord_) is *false* or _regexpRecord_.[[IgnoreCase]] is *false*, then 1. Assert: _extraWordChars_ is empty
- `sec-get-regexp.prototype.flags` @ `20`: `definition`: 1. Let _result_ be the empty String. 1. For each element _cu_ of _codeUnits_, do 1. Set _result_ to the string-concatenation of _result_ and
- `sec-isvalidregularexpressionliteral` @ `7.b`: `definition`: 1. Set _patternText_ to a new empty List. 1. For each integer _i_ such that 0 ≤ _i_ &lt; the length of _stringValue_, in ascending order, do
- `sec-regexpinitialize` @ `13.a`: `definition`: 1. Let _patternText_ be a new empty List. 1. For each integer _k_ such that 0 ≤ _k_ &lt; the length of _pattern_, in ascending order, do 1. 
- `sec-parsepattern-annexb` @ `4.a`: `definition`: 1. Let _parseResult_ be ParseText(_patternText_, |Pattern[~UnicodeMode, ~UnicodeSetsMode, ~NamedCaptureGroups]|).
- `sec-parsepattern-annexb` @ `4.b`: `definition`: 1. If _parseResult_ is a Parse Node and _parseResult_ Contains |GroupName|, then 1. Set _parseResult_ to ParseText(_patternText_, |Pattern[~
- `sec-runtime-semantics-characterrangeorunion-abstract-operation` @ `1.a.ii`: `definition`: 1. Return the union of CharSets _charSet_, _otherSet_, and _remainingSet_.
- `sec-runtime-semantics-repeatmatcher-abstract-operation` @ `4`: `definition`: 1. For each integer _k_ such that _parenIndex_ + 1 ≤ _k_ ≤ _parenIndex_ + _parenCount_, in ascending order, do 1. Set _capability_[_k_] to *
- `sec-compilepattern` @ `2.d`: `definition`: 1. Let _capability_ be OneIndexedList(_regexpRecord_.[[CapturingGroupsCount]], *undefined*).
- `sec-groupspecifiersthatmatch` @ `4`: `definition`: 1. For each element _groupSpecifier_ of ParseNodesWithin(_pattern_), do 1. If _groupSpecifier_ is a |GroupSpecifier| Parse Node, then 1. If 
- `sec-mightbothparticipate` @ `1`: `definition`: 1. Assert: NearestEnclosing(_x_, « |Pattern| ») is NearestEnclosing(_y_, « |Pattern| »).
- `sec-mightbothparticipate` @ `2`: `definition`: 1. For each element _d_ of ParseNodesWithin(NearestEnclosing(_x_, « |Pattern| »)), do 1. If _d_ is an instance of the production , then 1. L
- `sec-regexpbuiltinexec` @ `34.e 34.f`: `definition`: 1. Let _groupNameNode_ be CaptureGroupName(RegExpPattern(_regexp_), _i_). 1. If _groupNameNode_ is not ~empty~, then 1. Let _groupName_ be t
- `sec-compiletocharset` @ `1`: `definition`: 1. Let _escape_ be ParseGoal(StringToCodePoints(*"d"*), |CharacterClassEscape|, *false*, *false*, *false*). 1. Assert: _escape_ is an instan
- `sec-compiletocharset` @ `1`: `definition`: 1. Let _escape_ be ParseGoal(StringToCodePoints(*"s"*), |CharacterClassEscape|, *false*, *false*, *false*). 1. Assert: _escape_ is an instan
- `sec-compiletocharset` @ `1`: `definition`: 1. Let _escape_ be ParseGoal(StringToCodePoints(*"w"*), |CharacterClassEscape|, *false*, *false*, *false*). 1. Assert: _escape_ is an instan

### `context.emu` (2 reading entries)
- `sec-getactivescriptormodule` @ `3`: `definition`: 1. If _executionContext_ is ~empty~, return *null*.
- `sec-asyncgeneratoryield` @ `6`: `definition`: 1. Assert: ContextBelowTop() is not ~empty~.

### `dates.emu` (4 reading entries)
- `sec-date.prototype.toisostring` @ `6`: `definition`: 1. If IsDateTimeRepresentable(_tv_) is *false*, throw a *RangeError* exception.
- `sec-date.prototype.toisostring` @ `7`: `definition`: 1. Let _expanded_ be *true*. 1. If YearFromTime(_tv_) is in the inclusive interval from 0 to 9999, set _expanded_ to ExpandedYearForm(_tv_).
- `sec-makeday` @ `8`: `definition`: 1. Let _inLeapYear_ be DayFromYear(ℝ(_balancedYear_) + 1) - DayFromYear(ℝ(_balancedYear_)) - 365. 1. If _balancedMonthMV_ = 0, let _dayWithi
- `sec-date` @ `4.c.ii.2`: `definition`: 1. Let _tv_ be ParseDateString(_primitive_).

### `encodings.emu` (9 reading entries)
- `sec-numerictorawbytes` @ `1.a`: `definition`: 1. Let _rawBytes_ be LittleEndianBytes(IEEEBits(the result of converting _value_ to IEEE 754-2019 binary16 format using roundTiesToEven mode
- `sec-numerictorawbytes` @ `2.a`: `definition`: 1. Let _rawBytes_ be LittleEndianBytes(IEEEBits(the result of converting _value_ to IEEE 754-2019 binary32 format using roundTiesToEven mode
- `sec-numerictorawbytes` @ `3.a`: `definition`: 1. Let _rawBytes_ be LittleEndianBytes(IEEEBits(_value_, 11, 53), 8).
- `sec-numerictorawbytes` @ `4.d.i`: `definition`: 1. Let _rawBytes_ be LittleEndianBytes(_intValue_, _n_).
- `sec-numerictorawbytes` @ `4.e.i`: `definition`: 1. Let _rawBytes_ be LittleEndianBytes(_intValue_ modulo 2, _n_). 8 × _n_
- `sec-decodefulllengthbase64chunk` @ `1`: `definition`: 1. Let _standard_ be *"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"*. 1. Let _n_ be 0. 1. For each integer _i_ such tha
- `sec-uint8array.prototype.tobase64` @ `9.a`: `definition`: 1. Let _outAscii_ be StringToCodePoints(Base64Encode(_toEncode_, *"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"*, _omit
- `sec-uint8array.prototype.tobase64` @ `10.b`: `definition`: 1. Let _outAscii_ be StringToCodePoints(Base64Encode(_toEncode_, *"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"*, _omit
- `sec-numerictorawbytes` @ `4.b`: `definition`: 1. Let _conversionOperation_ be the Conversion Operation value specified in for Element Type _type_.

### `env.emu` (13 reading entries)
- `sec-runtime-semantics-catchclauseevaluation` @ `2`: `definition`: 1. Let _catchEnv_ be NewDeclarativeEnvironment(_oldEnv_). 1. Set _catchEnv_.[[CreatedFor]] to this Parse Node.
- `sec-declarative-environment-records-createmutablebinding-n-d` @ `2`: `definition`: 1. Perform AddBinding(_envRecord_, _name_, Record { [[Value]]: ~empty~, [[Mutable]]: *true*, [[Initialized]]: *false*, [[Strict]]: *false*, 
- `sec-declarative-environment-records-createimmutablebinding-n-s` @ `2`: `definition`: 1. Perform AddBinding(_envRecord_, _name_, Record { [[Value]]: ~empty~, [[Mutable]]: *false*, [[Initialized]]: *false*, [[Strict]]: _strict_
- `sec-declarative-environment-records-deletebinding-n` @ `2`: `definition`: 1. If BindingFor(_envRecord_, _name_).[[Deletable]] is *false*, return *false*.
- `sec-declarative-environment-records-deletebinding-n` @ `3`: `definition`: 1. Perform RemoveBinding(_envRecord_, _name_).
- `sec-declarative-environment-records-initializebinding-n-v` @ `2`: `definition`: 1. Set BindingFor(_envRecord_, _name_).[[Value]] to _value_.
- `sec-declarative-environment-records-initializebinding-n-v` @ `3`: `definition`: 1. Set BindingFor(_envRecord_, _name_).[[Initialized]] to *true*.
- `sec-declarative-environment-records-setmutablebinding-n-v-s` @ `4.a`: `definition`: 1. Set BindingFor(_envRecord_, _name_).[[Value]] to _value_.
- `sec-module-environment-records-getbindingvalue-n-s` @ `3 3.a`: `definition`: 1. If BindingFor(_envRecord_, _name_) is an indirect binding, then 1. Let _module_ be BindingFor(_envRecord_, _name_).[[Module]]. 1. Let _ta
- `sec-createimportbinding` @ `3`: `definition`: 1. Perform AddBinding(_envRecord_, _name_, Record { [[Value]]: ~empty~, [[Mutable]]: *false*, [[Initialized]]: *true*, [[Strict]]: *false*, 
- `sec-declarative-environment-records-initializebinding-n-v` @ `1`: `definition`: 1. Assert: _envRecord_ has a binding for _name_. 1. Assert: BindingFor(_envRecord_, _name_) is an uninitialized binding.
- `sec-declarative-environment-records-setmutablebinding-n-v-s` @ `5.a`: `definition`: 1. Assert: BindingFor(_envRecord_, _name_).[[Mutable]] is *false*.
- `sec-global-environment-records-initializebinding-n-v` @ `3`: `definition`: 1. Assert: _declRecord_ does not have a binding for _name_.

### `forin.emu` (1 reading entries)
- `sec-enumerate-object-properties` @ `1`: `definition`: 1. Let _history_ be a new empty List. 1. Let _closure_ be a new Abstract Closure with no parameters that captures _obj_ and _history_ and pe

### `host.emu` (20 reading entries)
- `sec-timezoneestring` @ `9`: `definition`: 1. Let _timeZoneName_ be TimeZoneNameSuffix(_tv_).
- `sec-atomics.pause` @ `1`: `definition`: 1. Perform SpinWaitHint().
- `sec-preparefortailcall` @ `2`: `definition`: 1. Perform DiscardContextResources(the running execution context).
- `sec-initializehostdefinedrealm` @ `11 12`: `definition`: 1. Let _global_ be HostGlobalObject(_realm_). 1. If _global_ is ~empty~, set _global_ to OrdinaryObjectCreate(_realm_.[[Intrinsics]].[[%Obje
- `sec-initializehostdefinedrealm` @ `13 14`: `definition`: 1. Let _thisValue_ be HostThisValue(_realm_). 1. If _thisValue_ is ~empty~, set _thisValue_ to _global_.
- `sec-initializehostdefinedrealm` @ `18`: `definition`: 1. Perform HostGlobalProperties(_realm_, _global_).
- `sec-initializehostdefinedrealm` @ `2`: `definition`: 1. Perform CreateIntrinsics(_realm_). 1. Perform HostExtendIntrinsics(_realm_).
- `sec-error-message` @ `5`: `definition`: 1. Perform HostExtendObject(_obj_). 1. Return _obj_.
- `sec-nativeerror` @ `5`: `definition`: 1. Perform HostExtendObject(_obj_). 1. Return _obj_.
- `sec-aggregate-error` @ `7`: `definition`: 1. Perform HostExtendObject(_obj_). 1. Return _obj_.
- `sec-suppressederror` @ `6`: `definition`: 1. Perform HostExtendObject(_obj_). 1. Return _obj_.
- `sec-host-cleanup-finalization-registry` @ `2`: `definition`: 1. If _cleanupResult_ is an abrupt completion, perform HostReportCleanupError(_cleanupResult_).
- `sec-cleanup-finalization-registry` @ `3`: `definition`: 1. Let _cell_ be MayCleanup(_finalizationRegistry_). 1. Repeat, while _cell_ is not ~empty~, 1. Remove _cell_ from _finalizationRegistry_.[[
- `sec-hostmakejobcallback` @ `1`: `definition`: 1. Return the JobCallback Record { [[Callback]]: _callback_, [[HostDefined]]: HostJobCallbackData(_callback_) }.
- `sec-hostcalljobcallback` @ `2`: `definition`: 1. Perform HostPrepareCallJobCallback(_jobCallback_). 1. Let _result_ be Completion(Call(_jobCallback_.[[Callback]], _thisValue_, _argList_)
- `sec-debugger-statement-runtime-semantics-evaluation` @ `1 1.a`: `definition`: 1. If DebuggerEnabled() is *true*, then 1. Perform DebuggerAction(). 1. Return a new implementation-defined Completion Record.
- `sec-function.prototype.tostring` @ `3`: `definition`: 1. If _func_ is a built-in function object, then 1. If _func_ has an [[InitialName]] internal slot and _func_.[[InitialName]] is a String, t
- `sec-function.prototype.tostring` @ `4`: `definition`: 1. If _func_ is an Object and IsCallable(_func_) is *true*, return NativeFunctionSource(_func_).
- `sec-escaperegexppattern` @ `4 5`: `definition`: 1. Let _escapedPattern_ be EscapePattern(_pattern_, _flags_).
- `sec-string.prototype.localecompare` @ `4`: `definition`: 1. Let _thatValue_ be ? ToString(_that_). 1. Return LocaleCompare(_string_, _thatValue_).

### `json.emu` (2 reading entries)
- `sec-ParseJSON` @ `1`: `definition`: 1. If IsJSONText(StringToCodePoints(_text_)) is *false*, throw a *SyntaxError* exception.
- `sec-shallowestcontainedjsonvalue` @ `2`: `definition`: 1. Let _parseSteps_ be ~empty~. 1. Set _parseSteps_ to the definition specified in . 1. Assert: _activeFunc_ is a built-in function object, 

### `lists.emu` (9 reading entries)
- `sec-GetImportedModule` @ `1`: `definition`: 1. Let _records_ be a new empty List. 1. For each LoadedModuleRequest Record _r_ of _referrer_.[[LoadedModules]], do 1. If ModuleRequestsEqu
- `sec-internalizejsonproperty` @ `5.c.ii.1`: `definition`: 1. Let _entryRecord_ be ~empty~. 1. For each element _entry_ of _entryRecords_, do 1. If _entryRecord_ is ~empty~ and _entry_.[[Key]] is _pr
- `sec-evaluate-import-call` @ `11.f`: `definition`: 1. Let _rest_ be a copy of _attrs_. 1. Let _sorted_ be a new empty List. 1. Repeat, while _rest_ is not empty, 1. Let _least_ be the first e
- `sec-withclausetoattributes` @ `2`: `definition`: 1. Let _rest_ be a copy of _attrs_. 1. Let _sorted_ be a new empty List. 1. Repeat, while _rest_ is not empty, 1. Let _least_ be the first e
- `sec-GetImportedModule` @ `2`: `definition`: 1. Assert: the number of elements in _records_ is 1.
- `sec-add-value-to-keyed-group` @ `1.a.i`: `definition`: 1. Assert: _groups_ contains exactly one Record _g_ such that SameValue(_g_.[[Key]], _key_) is *true*.
- `sec-getmodulenamespace` @ `1`: `definition`: 1. If _module_ is a Cyclic Module Record, then 1. Assert: _module_.[[Status]] is neither ~new~ nor ~unlinked~.
- `sec-innermoduleevaluation` @ `16.b.iv`: `definition`: 1. Assert: _requiredModule_.[[AsyncEvaluationOrder]] is an integer or _requiredModule_.[[AsyncEvaluationOrder]] is ~unset~.
- `sec-resolveexport` @ `7.a`: `definition`: 1. Assert: _module_ does not explicitly define an export named *"default"*.

### `memory.emu` (19 reading entries)
- `sec-composewriteeventbytes` @ `3.a`: `definition`: 1. Assert: _writeEvent_.[[ByteIndex]] ≤ _byteLocation_ &lt; _writeEvent_.[[ByteIndex]] + _writeEvent_.[[ElementSize]].
- `sec-copydatablockbytes` @ `1`: `definition`: 1. Assert: _fromBlock_ is not _toBlock_.
- `sec-getmodifysetvalueinbuffer` @ `3`: `definition`: 1. If IsBigIntElementType(_type_) is *true*, then 1. Assert: _value_ is a BigInt. 1. Else, 1. Assert: _value_ is a Number.
- `sec-getvaluefrombuffer` @ `7`: `definition`: 1. Assert: the number of elements in _rawValue_ is _elementSize_.
- `sec-getwaiterlist` @ `1`: `definition`: 1. Assert: 0 ≤ _i_ &lt; the number of bytes in _block_ and 0 ≤ _i_ + 3 &lt; the number of bytes in _block_.
- `sec-setvalueinbuffer` @ `3`: `definition`: 1. If IsBigIntElementType(_type_) is *true*, then 1. Assert: _value_ is a BigInt. 1. Else, 1. Assert: _value_ is a Number.
- `sec-tear-free-aligned-reads` @ `1.a.i`: `definition`: 1. Assert: the remainder of dividing _readEvent_.[[ByteIndex]] by _readEvent_.[[ElementSize]] is 0.
- `sec-frombase64` @ `10.a`: `definition`: 1. Assert: the number of elements in _bytes_ modulo 3 = 0.
- `sec-decode` @ `4.c.viii.5`: `definition`: 1. Assert: the number of elements in _octets_ is _n_.
- `sec-races` @ `1.a.i`: `definition`: 1. If _eventA_ is a WriteSharedMemory event or _eventA_ is a ReadModifyWriteSharedMemory event, then 1. If _eventB_ is a WriteSharedMemory e
- `sec-valid-chosen-reads` @ `1.g`: `definition`: 1. Let _someDiffers_ be *false*. 1. For each integer _i_ such that 0 ≤ _i_ &lt; _chosenLength_, in ascending order, do 1. If _chosenValue_[_
- `sec-createbytedatablock` @ `2`: `definition`: 1. If CanAllocate(_size_, *false*) is *false*, throw a *RangeError* exception. 1. Let _dataBlock_ be a new Data Block value consisting of _s
- `sec-createsharedbytedatablock` @ `1`: `definition`: 1. If CanAllocate(_size_, *true*) is *false*, throw a *RangeError* exception. 1. Let _dataBlock_ be DesignateShared(a new Data Block value c
- `sec-getrawbytesfromsharedblock` @ `6`: `definition`: 1. If the number of elements in _execution_.[[EventsRecords]] is 1, then 1. Let _rawValue_ be SingleAgentReadBytes(_execution_, _eventsRecor
- `sec-getmodifysetvalueinbuffer` @ `9.c`: `definition`: 1. If the number of elements in _execution_.[[EventsRecords]] is 1, then 1. Let _rawBytesRead_ be SingleAgentReadBytes(_execution_, _eventsR
- `sec-atomiccompareexchangeinsharedblock` @ `4`: `definition`: 1. If the number of elements in _execution_.[[EventsRecords]] is 1, then 1. Let _rawBytesRead_ be SingleAgentReadBytes(_execution_, _eventsR
- `sec-copydatablockbytes` @ `6.a.iv`: `definition`: 1. If the number of elements in _execution_.[[EventsRecords]] is 1, then 1. Let _bytes_ be SingleAgentReadBytes(_execution_, _eventsRecord_,
- `sec-allocatearraybuffer` @ `9.a`: `definition`: 1. If CanAllocate(_maxByteLength_, *false*) is *false*, throw a *RangeError* exception.
- `sec-sharedarraybuffer.prototype.grow` @ `12.f`: `definition`: 1. If CanAllocate(_byteLengthDelta_, *true*) is *false*, throw a *RangeError* exception.

### `numbers.emu` (22 reading entries)
- `sec-numeric-types-number-leftShift` @ `4`: `definition`: 1. Return 𝔽(ToFixedSizeInteger(ℝ(_leftNumber_) × 2, ~signed~, 32)). _shiftCount_
- `sec-numeric-types-number-signedRightShift` @ `4`: `definition`: 1. Return 𝔽(floor(ℝ(_leftNumber_) / 2)). _shiftCount_
- `sec-numeric-types-number-unsignedRightShift` @ `4`: `definition`: 1. Return 𝔽(floor(ℝ(_leftNumber_) / 2)). _shiftCount_
- `sec-numeric-types-number-bitwiseNOT` @ `2`: `definition`: 1. Return 𝔽(-ℝ(_oldValue_) - 1).
- `sec-number.prototype.tofixed` @ `11.a`: `definition`: 1. Let _intValue_ be floor(_number_ × 10 + 0.5). _fractionCount_
- `sec-number.prototype.toprecision` @ `11.a`: `definition`: 1. Let _exponent_ be 0. 1. Repeat, while 10 > _number_, 1. Set _exponent_ to _exponent_ - 1. 1. Repeat, while 10 ≤ _number_, 1. Set _exponen
- `sec-number.prototype.toexponential` @ `11.a.i`: `definition`: 1. Let _exponent_ be 0. 1. Repeat, while 10 > _number_, 1. Set _exponent_ to _exponent_ - 1. 1. Repeat, while 10 ≤ _number_, 1. Set _exponen
- `sec-math.hypot` @ `7`: `definition`: 1. Let _sum_ be 0. 1. For each element _number_ of _coerced_, do 1. Set _sum_ to _sum_ + ℝ(_number_) × ℝ(_number_). 1. Return an implementat
- `sec-numeric-types-number-exponentiate` @ `13`: `definition`: 1. Return ApproxPower(_base_, _exponent_).
- `sec-parseint-string-radix` @ `11`: `definition`: 1. Let _end_ be the length of _trimmedString_. 1. For each integer _i_ such that 0 ≤ _i_ &lt; the length of _trimmedString_, in descending o
- `sec-parseint-string-radix` @ `14`: `definition`: 1. Let _mathInt_ be 0. 1. For each integer _i_ such that 0 ≤ _i_ &lt; the length of _numberString_, in ascending order, do 1. Let _d_ be Rad
- `sec-numeric-types-number-tostring` @ `5`: `definition`: 1. Let _n_ be NumberDigitsExponent(_x_, _radix_). 1. Let _k_ be NumberDigitsCount(_x_, _radix_). 1. Let _s_ be NumberDigitsSignificand(_x_, 
- `sec-number.prototype.toexponential` @ `11.b.i`: `definition`: 1. Let _exponent_ be NumberDigitsExponent(𝔽(_number_), 10) - 1. 1. Let _ff_ be NumberDigitsCount(𝔽(_number_), 10) - 1. 1. Let _intSignifican
- `sec-numeric-types-number-unaryMinus` @ `2`: `definition`: 1. If _number_ is *+0*, return *-0*. 1. If _number_ is *-0*, return *+0*. 1. If _number_ is *+∞*, return *-∞*. 1. If _number_ is *-∞*, retur
- `sec-numeric-types-bigint-leftShift` @ `1`: `definition`: 1. If _y_ &lt; *0*, then 1. If _x_ is *0*, return *0*. 1. Let _bound_ be 4 × (DecimalExponent(abs(ℝ(_x_))) + 1). 1. If -ℝ(_y_) ≥ _bound_, th
- `sec-numeric-types-bigint-leftShift` @ `2`: `definition`: 1. If _x_ is *0* or _y_ is *0*, return _x_. 1. Return _x_ × *2*. ℤℤℤ_y_
- `sec-bigint.asuintn` @ `3`: `definition`: 1. If _bits_ = 0 or _bigint_ is *0*, return *0*. 1. If _bigint_ > *0* and _bits_ ≥ 4 × (DecimalExponent(ℝ(_bigint_)) + 1), return _bigint_. 
- `sec-bigint.asintn` @ `3 4 5`: `definition`: 1. If _bits_ = 0 or _bigint_ is *0*, return *0*. 1. Let _bound_ be 4 × (DecimalExponent(abs(ℝ(_bigint_))) + 1). 1. If _bits_ - 1 ≥ _bound_, 
- `sec-runtime-semantics-stringnumericvalue` @ `5`: `definition`: 1. Return RoundDecimalMV(_a_ × 10 + _b_, _e_ - _n_). _n_
- `sec-runtime-semantics-stringnumericvalue` @ `4`: `definition`: 1. Return RoundDecimalMV(_b_, _e_ - _n_).
- `sec-runtime-semantics-stringnumericvalue` @ `3`: `definition`: 1. Return RoundDecimalMV(_a_, _e_).
- `sec-numericvalue` @ `1`: `definition`: 1. Let _d_ be |DecimalLiteral|. 1. Assert: _d_ is a Parse Node. 1. If _d_ is an instance of the production or _d_ is an instance of the prod

### `object.emu` (17 reading entries)
- `sec-toobject` @ `2`: `definition`: 1. If _arg_ is a Boolean, then 1. Let _obj_ be OrdinaryObjectCreate(%Boolean.prototype%, « [[BooleanData]] »). 1. Set _obj_.[[BooleanData]] 
- `sec-toobject` @ `3`: `definition`: 1. If _arg_ is a Number, then 1. Let _obj_ be OrdinaryObjectCreate(%Number.prototype%, « [[NumberData]] »). 1. Set _obj_.[[NumberData]] to _
- `sec-toobject` @ `4`: `definition`: 1. If _arg_ is a String, return StringCreate(_arg_, %String.prototype%).
- `sec-toobject` @ `5`: `definition`: 1. If _arg_ is a Symbol, then 1. Let _obj_ be OrdinaryObjectCreate(%Symbol.prototype%, « [[SymbolData]] »). 1. Set _obj_.[[SymbolData]] to _
- `sec-toobject` @ `6`: `definition`: 1. If _arg_ is a BigInt, then 1. Let _obj_ be OrdinaryObjectCreate(%BigInt.prototype%, « [[BigIntData]] »). 1. Set _obj_.[[BigIntData]] to _
- `sec-arguments-exotic-objects-get-p-receiver` @ `4`: `definition`: 1. Assert: _map_ has an own property with key _propertyKey_.
- `sec-array` @ `10`: `definition`: 1. Assert: ℝ(OrdinaryGetOwnProperty(_array_, *"length"*).[[Value]]) = _numberOfArgs_.
- `sec-createmappedargumentsobject` @ `1`: `definition`: 1. Assert: IsSimpleParameterList of _formals_ is *true*.
- `sec-createnonenumerabledatapropertyorthrow` @ `1`: `definition`: 1. Assert: _obj_ is an extensible ordinary object with no non-configurable properties.
- `sec-definemethodproperty` @ `1`: `definition`: 1. Assert: _homeObj_ is an extensible ordinary object.
- `sec-functiondeclarationinstantiation` @ `20.d`: `definition`: 1. Assert: the VariableEnvironment of _calleeContext_ is _calleeEnv_.
- `sec-runtime-semantics-propertydefinitionevaluation` @ `4`: `definition`: 1. Assert: _obj_ is an extensible ordinary object with no non-configurable properties.
- `sec-runtime-semantics-propertydefinitionevaluation` @ `8`: `definition`: 1. Assert: _obj_ is an extensible ordinary object with no non-configurable properties.
- `sec-typedarray` @ `7.d.i`: `definition`: 1. Assert: _firstArg_ is an Object. 1. Assert: _firstArg_ does not have a [[TypedArrayName]] internal slot. 1. Assert: _firstArg_ does not h
- `sec-typedarraycreatefromconstructor` @ `3`: `definition`: 1. Assert: _ta_ has [[ViewedArrayBuffer]], [[TypedArrayName]], [[ContentType]], [[ByteLength]], [[ByteOffset]], and [[ArrayLength]] internal
- `sec-makebasicobject` @ `2`: `definition`: 1. Let _obj_ be MakeObject(_internalSlotsList_).
- `sec-createbuiltinfunction` @ `4`: `definition`: 1. Let _internalSlotsList_ be BuiltinFunctionSlots().

### `parse.emu` (19 reading entries)
- `sec-parsetext` @ `2 3 4 5`: `definition`: 1. Return ParseTextIn(_sourceText_, _goalSymbol_, *false*, *false*, *false*).
- `sec-parsefloat-string` @ `4`: `definition`: 1. Let _len_ be the length of _trimmedString_. 1. Let _i_ be 0. 1. If _i_ &lt; _len_, then 1. Let _sign_ be the numeric value of the code un
- `sec-parsehexoctet` @ `3 4 5 6 7 8`: `definition`: 1. Let _d0_ be RadixDigitValue(the code unit at index _position_ within _string_). 1. Let _d1_ be RadixDigitValue(the code unit at index _po
- `sec-performeval` @ `12`: `definition`: 1. If _direct_ is ~direct-eval~, let _directEval_ be *true*; else let _directEval_ be *false*. 1. Let _script_ be ParseTextIn(_sourceString_
- `sec-json.rawjson` @ `6`: `definition`: 1. Assert: _parseResult_.[[Value]] is either a String, a Number, or a Boolean, or _parseResult_.[[Value]] is *null*.
- `sec-performeval` @ `1`: `definition`: 1. Assert: _direct_ is ~direct-eval~ or _strictCaller_ is *false*.
- `sec-ParseJSON` @ `3`: `definition`: 1. Let _script_ be ParseTextIn(_scriptString_, |Script|, *false*, *true*, *false*).
- `sec-grouping-operator-runtime-semantics-evaluation` @ `1`: `definition`: 1. Return ? Evaluation of |Expression|.
- `sec-runtime-semantics-forin-div-ofbodyevaluation-lhs-stmt-iterator-lhskind-labelset` @ `8.g.ii.1`: `definition`: 1. Let _lhsRef_ be Completion(Evaluation of _lhs_).
- `sec-serializejsonobject` @ `1`: `definition`: 1. If _state_.[[Stack]] contains _value_, throw a *TypeError* exception.
- `sec-serializejsonobject` @ `10.a.i`: `definition`: 1. Let _properties_ be the empty String. 1. Let _first_ be *true*. 1. For each element _part_ of _partial_, do 1. If _first_ is *true*, set 
- `sec-serializejsonobject` @ `10.b.ii`: `definition`: 1. Let _properties_ be the empty String. 1. Let _first_ be *true*. 1. For each element _part_ of _partial_, do 1. If _first_ is *true*, set 
- `sec-serializejsonarray` @ `1`: `definition`: 1. If _state_.[[Stack]] contains _value_, throw a *TypeError* exception.
- `sec-serializejsonarray` @ `10.a.i`: `definition`: 1. Let _properties_ be the empty String. 1. Let _first_ be *true*. 1. For each element _part_ of _partial_, do 1. If _first_ is *true*, set 
- `sec-serializejsonarray` @ `10.b.ii`: `definition`: 1. Let _properties_ be the empty String. 1. Let _first_ be *true*. 1. For each element _part_ of _partial_, do 1. If _first_ is *true*, set 
- `sec-quotejsonstring` @ `2.a.i`: `definition`: 1. Set _product_ to the string-concatenation of _product_ and the Escape Sequence value specified in for Code Point _codePoint_.
- `sec-shallowestcontainedjsonvalue` @ `6.d.i.2.a`: `definition`: 1. If Parent(_candidate_) is not a |UnaryExpression| Parse Node, set _unaryExpr_ to _candidate_.
- `sec-shallowestcontainedjsonvalue` @ `6.d.i.3.a`: `definition`: 1. Assert: ParseNodesWithin(_unaryExpr_) contains _candidate_.
- `sec-shallowestcontainedjsonvalue` @ `6.d.ii.1`: `definition`: 1. Let _children_ be ChildNodes(_candidate_).

### `readings.emu` (44 reading entries)
- `sec-identifiers-static-semantics-early-errors`: It is a Syntax Error if the StringValue of |IdentifierName| is the String value of any terminal of |ReservedWord| except for `yield` or `await`.It is a Syntax Error if the StringVa
- `sec-patterns-static-semantics-early-errors`: It is a Syntax Error if the source text matched by |RegularExpressionModifiers| contains the same code point more than once.It is a Syntax Error if the source text matched by |Regu
- `sec-patterns-static-semantics-early-errors`: It is a Syntax Error if the source text matched by the first |RegularExpressionModifiers| and the source text matched by the second |RegularExpressionModifiers| are both empty.It i
- `sec-patterns-static-semantics-early-errors`: It is a Syntax Error if the source text matched by the first |RegularExpressionModifiers| contains the same code point more than once.It is a Syntax Error if the source text matche
- `sec-patterns-static-semantics-early-errors`: It is a Syntax Error if the source text matched by the second |RegularExpressionModifiers| contains the same code point more than once.It is a Syntax Error if the source text match
- `sec-patterns-static-semantics-early-errors`: It is a Syntax Error if any code point in the source text matched by the first |RegularExpressionModifiers| is also contained in the source text matched by the second |RegularExpre
- `sec-numeric-types-number-multiply` @ `6`: `proposed`: 1. If _x_ is *+0* and _y_ &lt; *-0*, return *-0*. 1. If _y_ is *+0* and _x_ &lt; *-0*, return *-0*. 1. Return 𝔽(ℝ(_x_) × ℝ(_y_)). 𝔽𝔽𝔽𝔽𝔽𝔽
- `sec-gather-available-ancestors` @ `1.a`: `proposed`: 1. If _execList_ does not contain _ancestorModule_ and _ancestorModule_.[[EvaluationError]] is ~empty~, then 1. Assert: _ancestorModule_.[[S
- `sec-builtincallorconstruct` @ `10.b.iii`: `test262 proposed`: 1. If _result_ is a normal completion, return ReturnCompletion(_result_.[[Value]]). 1. Return ? _result_.
- `sec-source-text-module-record-execute-module` @ `4.b`: `test262 proposed`: 1. Let _env_ be _module_.[[Environment]]. 1. Let _asyncBody_ be a new Abstract Closure with no parameters that captures _module_ and _env_ a
- `sec-parsetext` @ `5`: `proposed`: 1. Return « a newly created *SyntaxError* object ».
- `sec-parsepattern` @ `2.a`: `proposed`: 1. Let _parseResult_ be « a newly created *SyntaxError* object ».
- `sec-parsepattern-annexb` @ `1.a`: `proposed`: 1. Let _parseResult_ be « a newly created *SyntaxError* object ».
- `sec-dowait` @ `28.a`: `test262`: 1. Perform SuspendThisAgent(_waiterList_, _waiterRecord_). 1. If _waiterList_.[[Waiters]] contains _waiterRecord_, then 1. Set _waiterRecord | `proposed`: 1. Perform SuspendThisAgent(_waiterList_, _waiterRecord_). 1. If _waiterList_.[[Waiters]] contains _waiterRecord_, then 1. NOTE: The agent w
- `sec-enqueueatomicswaitasynctimeoutjob` @ `1.b.ii`: `proposed`: 1. Assert: _timeOfJobExecution_ ≥ 𝔽(_waiterRecord_.[[TimeoutTime]]) rounded down to an integral Number (ignoring potential non-monotonicity 
- `sec-enqueueatomicswaitasynctimeoutjob` @ `4`: `proposed`: 1. Let _delay_ be 𝔽(_waiterRecord_.[[TimeoutTime]]) - _now_. 1. If _delay_ &lt; *+0*, set _delay_ to *+0*. 1. Perform HostEnqueueTimeoutJob(
- `sec-utc-t` @ `1`: `proposed`: 1. If _t_ is not a finite Number, return *NaN*. 1. If MakeDay(𝔽(YearFromTime(_t_)), 𝔽(MonthFromTime(_t_)), *1*) is *NaN*, return *NaN*. 𝔽
- `sec-regexpbuiltinexec` @ `13.b`: `proposed`: 1. Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of _string_. 1. If _fullUnicode_ i
- `sec-asyncblockstart` @ `4`: `test262 proposed`: 1. Assert: _result_ is either ~unused~ or ~empty~.
- `sec-newpromisereactionjob` @ `1.h`: `proposed`: 1. If _handlerResult_ is an abrupt completion, then 1. Let _settleResult_ be Completion(Call(_promiseCapability_.[[Reject]], *undefined*, « 
- `sec-newpromisereactionjob` @ `1.i`: `proposed`: 1. If _settleResult_ is an abrupt completion, perform HostReportErrors(« _settleResult_.[[Value]] »). 1. Return ~empty~.
- `sec-function.prototype.tostring` @ `3`: `proposed`: 1. If _func_ is a built-in function object, return NativeFunctionSource(_func_).
- `sec-smr-Link` @ `1`: `proposed`: 1. If _module_.[[Environment]] is not ~empty~, return ~unused~. 1. Let _realm_ be _module_.[[Realm]].
- `sec-createdynamicfunction` @ `25`: `test262`: 1. If _expr_ is a List of errors, throw a *SyntaxError* exception. 1. If AllPrivateIdentifiersValid of _body_ with argument « » is *false*,  | `proposed`: 1. If _expr_ is a List of errors, throw a *SyntaxError* exception. 1. If AllPrivateIdentifiersValid of _body_ with argument « » is *false*, 
- `sec-compiletocharset` @ `2`: `test262 proposed`: 1. If _s_ is a Unicode property value or property value alias for the General_Category (gc) property listed in , then 1. Let _v_ be UnicodeM
- `sec-allocatesharedarraybuffer` @ `9.c`: `test262 proposed`: 1. Let _agentRecord_ be the Agent Record of the surrounding agent. 1. Let _rawBytes_ be NumericToRawBytes(~biguint64~, ℤ(_byteLength_), _age
- `sec-static-semantics-contains` @ `1.a`: `test262 proposed`: 1. If _child_ is an instance of _symbol_, return *true*. 1. If _symbol_ is |AwaitExpression| and this Parse Node is an instance of the produ
- `sec-string.prototype.split` @ `10.d`: `test262 proposed`: 1. Let _codeUnits_ be a new empty List. 1. For each integer _i_ such that 0 ≤ _i_ &lt; _outLength_, in ascending order, do 1. Append the sub
- `sec-createintrinsics` @ `2`: `test262 proposed`: 1. Let _entries_ be IntrinsicObjects(). 1. Let _objects_ be a new empty List. 1. For each Record _entry_ of _entries_, do 1. If _entry_.[[Pr
- `sec-sortindexedproperties` @ `4`: `test262 proposed`: 1. Let _next_ be SortStep(the number of elements in _items_, ~empty~, ~empty~). 1. Repeat, while _next_ is a List, 1. Let _result_ be _sortC
- `sec-finalization-registry.prototype.unregister` @ `5`: `test262 proposed`: 1. Let _cells_ be a copy of _finalizationRegistry_.[[Cells]]. 1. For each Record { [[WeakRefTarget]], [[HeldValue]], [[UnregisterToken]] } _
- `sec-patterns-static-semantics-is-character-class-annexb`: `test262 proposed`: 1. Return *false*.
- `sec-numeric-types-bigint-exponentiate` @ `3`: `proposed`: 1. If BigIntTooLarge(*"exponentiate"*, _base_, _exponent_) is *true*, throw a *RangeError* exception. 1. Return _base_ raised to the power _
- `sec-numeric-types-bigint-leftShift` @ `2`: `proposed`: 1. If _x_ is *0* or _y_ is *0*, return _x_. 1. If BigIntTooLarge(*"leftShift"*, _x_, _y_) is *true*, throw a *RangeError* exception. 1. Retu
- `sec-numeric-types-bigint-multiply` @ `1`: `proposed`: 1. If BigIntTooLarge(*"multiply"*, _x_, _y_) is *true*, throw a *RangeError* exception. 1. Return _x_ × _y_.
- `sec-numeric-types-bigint-add` @ `1`: `proposed`: 1. If BigIntTooLarge(*"add"*, _x_, _y_) is *true*, throw a *RangeError* exception. 1. Return _x_ + _y_.
- `sec-numeric-types-bigint-subtract` @ `1`: `proposed`: 1. If BigIntTooLarge(*"subtract"*, _x_, _y_) is *true*, throw a *RangeError* exception. 1. Return _x_ - _y_.
- `sec-bigint.asuintn` @ `3`: `proposed`: 1. If _bits_ = 0 or _bigint_ is *0*, return *0*. 1. If _bigint_ > *0* and _bits_ ≥ 4 × (DecimalExponent(ℝ(_bigint_)) + 1), return _bigint_. 
- `sec-string.prototype.repeat` @ `7`: `proposed`: 1. If StringTooLarge(_n_ × the length of _string_) is *true*, throw a *RangeError* exception. 1. Return the String value that is made from _
- `sec-stringpaddingbuiltinsimpl` @ `7`: `proposed`: 1. If _fillString_ is not the empty String and StringTooLarge(_intMaxLength_) is *true*, throw a *RangeError* exception. 1. Return StringPad
- `sec-string.prototype.concat` @ `5.b`: `proposed`: 1. If StringTooLarge(the length of _result_ + the length of _nextString_) is *true*, throw a *RangeError* exception. 1. Set _result_ to the 
- `sec-applystringornumericbinaryoperator` @ `1.c.iii`: `proposed`: 1. If StringTooLarge(the length of _leftString_ + the length of _rightString_) is *true*, throw a *RangeError* exception. 1. Return the stri
- `sec-joinindexedproperties` @ `4.a`: `proposed`: 1. If _k_ > 0, then 1. If StringTooLarge(the length of _result_ + the length of _separator_) is *true*, throw a *RangeError* exception. 1. S
- `sec-joinindexedproperties` @ `4.d.iii`: `proposed`: 1. If StringTooLarge(the length of _result_ + the length of _elementString_) is *true*, throw a *RangeError* exception. 1. Set _result_ to t

### `realm.emu` (7 reading entries)
- `sec-createintrinsics` @ `2`: `definition`: 1. Let _entries_ be IntrinsicObjects(). 1. Let _objects_ be a new empty List. 1. For each Record _entry_ of _entries_, do 1. If _entry_.[[Pr
- `sec-setdefaultglobalbindings` @ `2`: `definition`: 1. For each Record _p_ of PropertyOrder(_global_, ClauseProperties(_global_, )), do 1. If PropertyProvided(_p_) is *true*, then 1. Let _name
- `sec-modulenamespacecreate` @ `8`: `definition`: 1. For each Record _p_ of PropertyOrder(_namespace_, ClauseProperties(_namespace_, )), do 1. Perform OwnPropertyCreate(_namespace_, _p_.[[Ke
- `sec-getprototypefromconstructor` @ `1`: `definition`: 1. Assert: IsIntrinsicName(_intrinsicDefaultProto_) is *true*. 1. Assert: The corresponding object must be an intrinsic that is intended to 
- `sec-ordinarycreatefromconstructor` @ `1`: `definition`: 1. Assert: IsIntrinsicName(_intrinsicDefaultProto_) is *true*. 1. Assert: The corresponding object must be an intrinsic that is intended to 
- `sec-getprototypefromconstructor` @ `6`: `definition`: 1. Return RealmIntrinsic(_realm_, _intrinsicDefaultProto_).
- `sec-addrestrictedfunctionproperties` @ `1`: `definition`: 1. Assert: _realm_.[[Intrinsics]] has a [[%ThrowTypeError%]] field and _realm_.[[Intrinsics]].[[%ThrowTypeError%]] is an Object.

### `sort.emu` (1 reading entries)
- `sec-sortindexedproperties` @ `4`: `definition`: 1. Let _next_ be SortStep(the number of elements in _items_, ~empty~, ~empty~). 1. Repeat, while _next_ is a List, 1. Let _result_ be _sortC

### `strings.emu` (4 reading entries)
- `sec-string.prototype.tolowercase` @ `5`: `definition`: 1. Let _lowerText_ be toLowercase(_sText_).
- `sec-createdynamicfunction` @ `13.c.ii`: `definition`: 1. Set _joinedParamsString_ to the string-concatenation of _joinedParamsString_, *","*, and _nextArgString_.
- `sec-string.prototype.normalize` @ `7`: `definition`: 1. Let _normal_ be UnicodeNormalize(_string_, _form_).
- `sec-encodeforregexpescape` @ `5.e`: `definition`: 1. For each integer _i_ such that 0 ≤ _i_ &lt; the length of _codeUnits_, in ascending order, do 1. Let _codeUnit_ be the code unit at index

### `syntax.emu` (12 reading entries)
- `sec-object-initializer-static-semantics-early-errors`: It is a Syntax Error if ProtoPropertyCount(|PropertyDefinitionList|) ≥ 2. This rule is not applied if this |ObjectLiteral| is contained within a |Script| that is being parsed for P
- `sec-class-definitions-static-semantics-early-errors`: It is a Syntax Error if the PrivateBoundIdentifiers of |ClassElementList| contains any duplicate entries, unless PrivateDuplicatesAreAccessorPairs(|ClassElementList|) is *true*.
- `sec-block-static-semantics-early-errors`: It is a Syntax Error if the LexicallyDeclaredNames of |StatementList| contains any duplicate entries., unless the host is a web browser or otherwise supports , and both of the foll
- `sec-switch-statement-static-semantics-early-errors`: It is a Syntax Error if the LexicallyDeclaredNames of |CaseBlock| contains any duplicate entries., unless the host is a web browser or otherwise supports , and both of the followin
- `sec-isintailposition` @ `2 3`: `definition`: 1. If NearestEnclosing(_call_, « |FunctionBody|, |ConciseBody|, |AsyncConciseBody| ») is ~empty~, return *false*. 1. Let _body_ be NearestEn
- `sec-runtime-semantics-methoddefinitionevaluation` @ `5`: `definition`: 1. Let _formalParamList_ be ParseGoal(« », |FormalParameters|, *false*, *false*, *false*). 1. Assert: _formalParamList_ is an instance of th
- `sec-runtime-semantics-classfielddefinitionevaluation` @ `2.a`: `definition`: 1. Let _formalParamList_ be ParseGoal(« », |FormalParameters|, *false*, *false*, *false*). 1. Assert: _formalParamList_ is an instance of th
- `sec-runtime-semantics-classstaticblockdefinitionevaluation` @ `4`: `definition`: 1. Let _formalParams_ be ParseGoal(« », |FormalParameters|, *false*, *false*, *false*). 1. Assert: _formalParams_ is an instance of the prod
- `sec-static-semantics-lexicallydeclarednames` @ `1`: `definition`: 1. If |ExportDeclaration| is , return a new empty List. ExportDeclaration : `export` VariableStatement
- `sec-static-semantics-vardeclarednames` @ `1`: `definition`: 1. If |ExportDeclaration| is , return the BoundNames of |ExportDeclaration|. ExportDeclaration : `export` VariableStatement
- `sec-static-semantics-varscopeddeclarations` @ `1`: `definition`: 1. If |ExportDeclaration| is , return the VarScopedDeclarations of the |VariableStatement| of |ExportDeclaration|. ExportDeclaration : `expo
- `sec-static-semantics-propname`: `default`: 1. Return the StringValue of the |IdentifierReference| of |CoverInitializedName|.

### `tables.emu` (4 reading entries)
- `sec-encodeforregexpescape` @ `2.a`: `definition`: 1. Return the string-concatenation of 0x005C (REVERSE SOLIDUS) and the ControlEscape value specified in for Code Point _codePoint_.
- `sec-patterns-static-semantics-character-value` @ `1`: `definition`: 1. Return TableLookup(, *"Numeric Value"*, *"ControlEscape"*, CodePointsToString(the source text matched by |ControlEscape|)).
- `sec-runtime-semantics-unicodematchproperty-p` @ `3`: `definition`: 1. If _p_ is a or property alias listed in the “” column of , let _t_ be ; else let _t_ be . 1. Let _c_ be TableLookup(_t_, *"Canonical prop
- `sec-runtime-semantics-unicodematchpropertyvalue-p-v` @ `3`: `definition`: 1. Let _value_ be CanonicalPropertyValue(_p_, _v_).

### `timezones.emu` (5 reading entries)
- `sec-availablenamedtimezoneidentifiers` @ `1`: `definition`: 1. If HasTimeZoneRules() is *false*, then 1. Return « the Time Zone Identifier Record { [[Identifier]]: *"UTC"*, [[PrimaryIdentifier]]: *"UT
- `sec-availablenamedtimezoneidentifiers` @ `2`: `definition`: 1. Let _identifiers_ be AvailableNamedTimeZoneIds().
- `sec-availablenamedtimezoneidentifiers` @ `4.b 4.b.i`: `definition`: 1. If IsNonPrimaryTimeZoneId(_identifier_) is *true* and _identifier_ is not *"UTC"*, then 1. Set _primary_ to PrimaryTimeZoneId(_identifier
- `sec-systemtimezoneidentifier` @ `1`: `definition`: 1. If SupportsOnlyUTC() is *true*, return *"UTC"*.
- `sec-utc-t` @ `4.d.ii`: `definition`: 1. Let _tBefore_ be LastTransitionBefore(_systemTimeZoneIdentifier_, _t_). 1. Let _possibleInstantsBefore_ be GetNamedTimeZoneEpochNanosecon

## 4. Unchecked Assertions & Constructive Choices
### Constructive Choice Sites (`choice-sites.txt`)
Non-constructive mathematical choice expressions (`Expr.such` / `Expr.extreme`) were lowered constructively or verified against monotonic bounds:
- `sec-yearfromtime 1	the largest integer y with TimeFromYear(y) ≤ tv: TimeFromYear is increasing`

### Unchecked / Deferred Assertions (`permanent.emu`, 23 entries)
- `sec-arguments-exotic-objects-defineownproperty-p-desc` @ step `7.b.i.1` (class `assert-future`): The success of the following Set, a later step, for the reason that mapped formal parameters are writable.
- `sec-arguments-exotic-objects-set-p-v-receiver` @ step `3.a` (class `assert-future`): The success of the following Set, a later step, for the reason that mapped formal parameters are writable.
- `sec-createimportbinding` @ step `2` (class `assert-future`): What _targetModule_.[[Environment]] will have once it is instantiated, a later state.
- `sec-date` @ step `4.c.ii.1` (class `assert-future`): The next step's completion, for the reason that _primitive_ is a String.
- `sec-evaldeclarationinstantiation` @ step `3.c` (class `assert-future`): Termination of the following loop.
- `sec-evaldeclarationinstantiation` @ step `13.b.ii.3` (class `assert-future`): Termination of the following loop.
- `sec-getexportednames` @ step `3.a` (class `assert-provenance`): Why _module_ is in _exportStarSet_ (the start of an export-star cycle), not a further test.
- `sec-makebasicobject` @ step `6` (class `assert-future`): Conditioned on which internal methods the caller will later override.
- `sec-makebasicobject` @ step `7` (class `assert-future`): Conditioned on which internal methods the caller will later override.
- `sec-moduleevaluation` @ step `1` (class `assert-provenance`): About the surrounding agent's other calls to Evaluate, which the state at the step does not record.
- `sec-ordinarysetwithowndescriptor` @ step `2.d.i` (class `assert-provenance`): Rests on _receiver_'s [[GetOwnProperty]] answer just before; a Proxy receiver need not keep it, so the Assert is vacuous there (a drafted spec issue).
- `sec-preparefortailcall` @ step `1` (class `assert-future`): What later evaluation will and will not use the current execution context for.
- `sec-resolveexport` @ step `3.a.i` (class `assert-provenance`): Why the request is in _resolveSet_ (a circular import), not a further test.
- `sec-resolveexport` @ step `9.e.iii.1` (class `assert-provenance`): Why this branch is reached (a second star export resolves the name), not a further test.
- `sec-runtime-semantics-classdefinitionevaluation` @ step `6.a.i.1` (class `assert-provenance`): Why a duplicate private name can occur (a getter/setter pair), which the early errors guarantee.
- `sec-runtime-semantics-evaluateclassstaticblockbody` @ step `1` (class `assert-provenance`): Which step created _funcObj_ is its origin, not a property of the function object.
- `erratum-AtomicsWaitAsyncTimeoutAssert/sec-enqueueatomicswaitasynctimeoutjob@1.b.ii/proposed` @ step `1` (class `assert-provenance`): Compares the host's clock readings while ignoring their non-monotonicity, which the state does not give.
- `definition-sec-getprototypefromconstructor-1/sec-getprototypefromconstructor@1/definition` @ step `2` (class `assert-provenance`): What the caller intends the intrinsic object for, not a property of the object or the state.
- `definition-sec-ordinarycreatefromconstructor-1/sec-ordinarycreatefromconstructor@1/definition` @ step `2` (class `assert-provenance`): What the caller intends the intrinsic object for, not a property of the object or the state.
- `sort-extensible` @ step `2` (class `history`): Whether an object without an [[Extensible]] internal slot has been observed to return *false* from [[IsExtensible]] or *true* from [[PreventExtensions]]: the answers of earlier calls, which the state does not record.
- `ph-twenty-significant-digits` @ step `2` (class `assert-provenance`): _n_ is a decimal literal's value at every use; an existential over all integers with no test over an abstract mathematical value.
- `sec-number.prototype.toexponential#1` @ step `1` (class `informative`): The NOTE's alternative to the step choosing _exponent_, _intSignificand_ and _ff_, recommended as a guideline only.
- `sec-numeric-types-number-tostring#1` @ step `1` (class `informative`): The NOTE's alternative to the step choosing _n_, _k_ and _s_, recommended as a guideline only.

## 5. Interpreting Readings & Interpreting Phrase Meanings

### Interpreting readings (26 entries)

#### `early-errors-cover-first`
- **Spec**: sec-syntactic-grammar (spec.html 401-410); sec-static-semantic-rules (spec.html 883); sec-parsetext 2-5 (spec.html 16439-16442); sec-arrow-function-definitions-static-semantics-early-errors (spec.html 24081-24097); sec-async-arrow-function-definitions-static-semantics-early-errors (spec.html 25808-25812)
- **Quote**: |CoverCallExpressionAndAsyncArrowHead| must cover an |AsyncArrowHead|.
- **Ambiguity**: When a cover does not cover the nonterminal a rule says it must, the other rules of that production and of the productions above it still apply, and their conditions read static semantics through the cover (Contains, BoundNames, IsSimpleParameterList), whose rows take "the |n| that is covered by" it: a node that does not exist (`([...x = []]) => {}`, `async (...x = []) => {}`). The text orders no rules and skips none.
- **Decision**: Option A, in two halves. (1) EarlyErrorsOf applies a node's rules only when the nodes it contains have no early errors. (2) Early Errors of a node applies its own "must cover" rules first, and its other rules only when those report none (AsyncArrowFunction's rules beside its own cover rule); a covered node's rules are applied as EarlyErrorsOf applies them. The List is then not every early error, but it is non-empty exactly when there is one. Not an erratum: a cover that fails its "must cover" rule already makes the program an early SyntaxError, and ParseText leaves the number and order of the errors implementation-defined, so no program's result depends on the order; the reading takes the one order in which no rule reads through a cover that covers nothing.
- **Scope**: every early-error check (ParseTextIn); it changes results only where the literal reading stops.

#### `propname-coverinitializedname`
- **Spec**: sec-static-semantics-propname (spec.html 10111-10195)
- **Quote**: PropName ( ): a String or ~empty~
- **Ambiguity**: PropName has no row for CoverInitializedName, and PropertyNameList asks for it.
- **Decision**: The row of the shorthand IdentifierReference twin (syntax.emu); no answer depends on it, so it is a reading, not an erratum. The missing row is never asked: under early-errors-cover-first the ObjectLiteral's `__proto__` rule, PropertyNameList's only asker, applies only when the nodes it contains have no early error, and a CoverInitializedName always has one.
- **Scope**: ObjectLiteral early errors.

#### `annexb-regexp-extension`
- **Spec**: sec-patterns-static-semantics-early-errors-annexb (spec.html 53971); sec-compiletocharset-annexb (spec.html 54232-54233); sec-compiletocharset-annexb (spec.html 54082); sec-parsepattern-annexb (spec.html 54118); sec-countleftcapturingparens-annexb (spec.html 53994); sec-compilesubpattern-annexb (spec.html 54032-54034); sec-compileatom-annexb (spec.html 54047)
- **Quote**: the rules for the following productions are modified with the addition of the highlighted text … The semantics of CompileToCharSet with argument _regexpRecord_ is extended as follows: … Two rules are replaced: … The following rules are also added: … is extended as follows, with modifications highlighted
- **Ambiguity**: B.1.2's clauses extend operations of §22.2 ("is extended as follows"), add rules, replace two rules, modify two productions' early rules and give ParsePattern a modified body, while the annex is optional off a web browser: the text says neither how the extended and the plain operation stand in one specification nor that the choice holds for the whole run.
- **Decision**: An annex row on a production without a main row of its SDO (B.1.2's added rules, B.3.5's rows) is a row of the SDO (Ecma.SdoRow.annex), reached only where the annex grammar parsed. A replaced rule (CompileToCharSet on NonemptyClassRanges and NonemptyClassRangesNoDash) and ParsePattern's modified body are reached through overlay step patches (spec/formal/annexb.emu) on the main algorithms: a first step "if the host is a web browser or otherwise supports B.1.2", asking the host about sec-regular-expressions-patterns as the parse does, under which the annex row's steps run (CompileToCharSet) or the annex algorithm is returned (ParsePattern); off it the main steps run, and the annex CompileToCharSet rows stay shadowed (Ecma.SdoRow.mainLast). B.1.2.1's modified early rules stand for the main rules of their productions (Ecma.EarlyRow.modifies); their highlighted conditions apply on a B.1.2 host only, so off it they are the main rules. The answer is a fact of the run (Ecma.Host.OptionalLaws.webBrowser): the same at every call with the same arguments, the state unchanged. B.1.2.5-B.1.2.7's prose rules ("the same as … with |X| substituted for |Atom|") are overlay row readings (annexb.emu) on productions only the B.1.2 grammar has, so the ParsePattern gate is theirs too. B.1.2.2's reinterpreted references in CountLeftCapturingParensWithin and CountLeftCapturingParensBefore are definition readings counting |Atom|'s and |ExtendedAtom|'s group nodes with no host query: off a B.1.2 host no |ExtendedAtom| node exists, so the count is the main text's.
- **Scope**: Annex B hosts, B.1.2.

#### `annexb-quantifiableassertion-compile`
- **Spec**: sec-compilesubpattern-annexb (spec.html 54032); sec-compilesubpattern (spec.html 37962-37964); sec-compileassertion-annexb (spec.html 54040-54041)
- **Quote**: is the same as for Term :: Atom Quantifier but with |QuantifiableAssertion| substituted for |Atom|
- **Ambiguity**: Term :: Atom Quantifier's first step is "Let _m_ be CompileAtom of |Atom| with arguments _regexpRecord_ and _direction_". Substituting |QuantifiableAssertion| for |Atom| in it asks CompileAtom of a |QuantifiableAssertion|, for which CompileAtom has no rule (the chain falls to |Disjunction| and stops), while B.1.2.6 gives |QuantifiableAssertion| CompileAssertion rules. "Substituted" is not defined.
- **Decision**: The substitution takes the operation of the substituted nonterminal's rules with it: _m_ is CompileAssertion of |QuantifiableAssertion| with argument _regexpRecord_ (CompileAssertion takes no _direction_, as Term :: Assertion's rule shows); the other steps substitute |QuantifiableAssertion| for |Atom|.
- **Scope**: Annex B hosts, a quantified lookahead (`/(?=a)*/`) in a pattern without the u or v flag.

#### `makeday-time-value-range`
- **Spec**: sec-makeday 8 (spec.html 34380)
- **Quote**: Find a finite time value _tv_ such that YearFromTime(_tv_) = ℝ(_balancedYear_)
- **Ambiguity**: "Find a finite time value _tv_ such that …" leaves open whether "time value" is the definition (any finite integral Number) or the ±8.64 × 10^15 range.
- **Decision**: The definition. The callers' TimeClip applies the range, as the three engines do. The Find fixes only Day(_tv_): every _tv_ that meets it has Day(_tv_) = DayFromYear(_balancedYear_) + the month's start, and step 9 reads only Day(_tv_). FirstDayOf answers the least such _tv_ (a choice the text leaves open, unobservable), and NaN exactly when none exists.
- **Scope**: Date arithmetic near the range bounds.

#### `native-function-empty-initial-name`
- **Spec**: sec-function.prototype.tostring 3 (spec.html 31669)
- **Quote**: if _func_ has an [[InitialName]] internal slot and _func_.[[InitialName]] is a String, the portion of
- **Ambiguity**: For an empty [[InitialName]], the step asks that the portion matched by NativeFunctionAccessor? PropertyName be the empty String; a NativeFunction without a PropertyName has no such portion.
- **Decision**: The portion of a NativeFunction without a NativeFunctionAccessor or a PropertyName is empty, so an empty [[InitialName]] is met by one (`function () { [native code] }`): step 3 answers NativeFunctionSource, whose law then asks for such a String. Any other [[InitialName]] meets it when it is `get` or `set` (the NativeFunction is ambiguous; either way the portion is the name), or when `function `, it and `() { [native code] }` parse as a NativeFunction whose NativeFunctionAccessor? PropertyName portion is all of it. The erratum NativeFunctionInitialName (row native-function-initial-name) covers the names no String meets.
- **Scope**: Function.prototype.toString of built-ins with an empty or unusual [[InitialName]] (anonymous built-ins).

#### `parse-node-contains`
- **Spec**: sec-groupspecifiersthatmatch 4 (spec.html 37716); sec-mightbothparticipate 2 (spec.html 37359); sec-countleftcapturingparenswithin (spec.html 37324); sec-countleftcapturingparensbefore (spec.html 37344); sec-patterns-static-semantics-early-errors (spec.html 37181); sec-parsetimezoneoffsetstring (spec.html 34692); sec-continue-statement-static-semantics-early-errors (spec.html 22971); sec-break-statement-static-semantics-early-errors (spec.html 23004); sec-regexpbuiltinexec (spec.html 39852)
- **Quote**: Parse Nodes contained within _parseNode_. … not nested, directly or indirectly (but not crossing function or `static` initialization block boundaries), within an |IterationStatement|. … If _regexp_ contains any |GroupName|, then
- **Ambiguity**: "contained within" / "contain" for Parse Nodes and "the derived |X|" (12 uses) are never defined; nor are "occur before", "nested, directly or indirectly (but not crossing function … boundaries), within", or what a RegExp object "contains".
- **Decision**: A node is contained within another when it is that node or a node it contains (reflexive descendant): "the |X| Parse Node(s) contained within _n_" search _n_ too; "_x_ is contained within a |X|" and "_n_ contains a |X|" exclude the node itself. A node occurs before _a_ when it precedes _a_ in source order (a node before its children) and does not contain it. Nesting stops at the nearest |FunctionBody| or |ClassStaticBlockBody|. A RegExp instance contains what its |Pattern| contains. The derived |Disjunction| is the one the step names; GroupSpecifiersThatMatch lists them in source order.
- **Scope**: Parse Node containment in early errors and static semantics; RegExpBuiltinExec's group names.

#### `catch-env-created-for`
- **Spec**: sec-runtime-semantics-catchclauseevaluation 2 (spec.html 23461); sec-evaldeclarationinstantiation (spec.html 30246-30293)
- **Quote**: Let _catchEnv_ be NewDeclarativeEnvironment(_oldEnv_). … If _thisEnv_ is not the Environment Record for a |Catch| clause, throw a *SyntaxError* exception.
- **Ambiguity**: "the Environment Record for a |Catch| clause" is read elsewhere, but nothing records which Catch an environment is for.
- **Decision**: The step also records the Catch (a [[CreatedFor]] field) that _catchEnv_ is for; "is not the Environment Record for a |Catch| clause" tests that field.
- **Scope**: Annex B catch-parameter redeclaration.

#### `forin-iterator-host-model`
- **Spec**: sec-enumerate-object-properties 1 (spec.html 22780)
- **Quote**: Return an iterator object whose `next` method iterates over all the String-valued keys of enumerable properties of _obj_. The iterator object is never directly accessible to ECMAScript code.
- **Ambiguity**: EnumerateObjectProperties returns an implementation-defined iterator, constrained by prose rules on properties and their order.
- **Decision**: A closure whose internal method calls the host chooses (ForInStep); [[Prototype]], throw and return are unobservable and absent; an abrupt call is returned from `next`.
- **Scope**: for-in.

#### `json-parse-any-realm`
- **Spec**: sec-shallowestcontainedjsonvalue 2 (spec.html 47766)
- **Quote**: Assert: _activeFunc_ is a `JSON.parse` built-in function object
- **Ambiguity**: "%JSON.parse%" names the intrinsic of one realm; the step tests whether a function is JSON.parse.
- **Decision**: A JSON.parse built-in of any realm (its behaviour is the algorithm of JSON.parse).
- **Scope**: JSON.parse source text access.

#### `assert-wording`
- **Spec**: sec-getmodulenamespace 1 (spec.html 29324); sec-resolveexport 7.a (spec.html 28849); sec-getwaiterlist 1 (spec.html 46931); sec-addrestrictedfunctionproperties 1 (spec.html 13747)
- **Quote**: is not ~new~ or ~unlinked~. … was not explicitly defined by this module. … are valid byte offsets within the memory of _block_. … exists and has been initialized.
- **Ambiguity**: Asserts in undefined terms: "is not ~new~ or ~unlinked~", "explicitly defined", "valid byte offsets within the memory of", "has been initialized" (of an Intrinsics field, which has no initialized state).
- **Decision**: Neither value; an ExportEntry of [[LocalExportEntries]] or [[IndirectExportEntries]] with that name; an index of one of the block's bytes; the field exists and is an Object.
- **Scope**: those Asserts.

#### `number-shift-width`
- **Spec**: sec-numeric-types-number-leftShift 4 (spec.html 1952); sec-numeric-types-number-signedRightShift 4 (spec.html 1969); sec-numeric-types-number-unsignedRightShift 4 (spec.html 1986); sec-numeric-types-number-bitwiseNOT 2 (spec.html 1738)
- **Quote**: Return the result of left shifting _leftNumber_ by _shiftCount_ bits. The mathematical value of the result is exactly representable as a 32-bit two's complement bit string.
- **Ambiguity**: "the result of left shifting _x_ by _n_ bits" is an informal operation; its width comes only from a range sentence.
- **Decision**: Arithmetic on the 32-bit view: ToFixedSizeInteger(x × 2^n) for left shift, floor(x / 2^n) for the right shifts, -x - 1 for NOT.
- **Scope**: Number shift and NOT operators.

#### `parseint-radix-digit`
- **Spec**: sec-parseint-string-radix 11 (spec.html 30422)
- **Quote**: If _trimmedString_ contains a code unit that is not a radix-_radixMV_ digit
- **Ambiguity**: "a radix-_R_ digit" is only implied by step 14's letter values.
- **Decision**: A code unit whose RadixDigitValue is below the radix.
- **Scope**: parseInt.

#### `parseint-significant-digits`
- **Spec**: sec-parseint-string-radix 14 (spec.html 30425)
- **Quote**: contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit
- **Ambiguity**: The parenthesis allows replacing "every significant digit after the 20th" by 0 and, in other radices, an approximation: two latitudes.
- **Decision**: One implementation-defined choice (truncation after 20 digits; every partial replacement gives the same Number); in other radices the host approximates.
- **Scope**: parseInt of long numerals.

#### `number-tostring-last-digit`
- **Spec**: sec-numeric-types-number-tostring 5 (spec.html 2154); sec-number.prototype.toexponential 11.b.i (spec.html 32761)
- **Quote**: and _k_ is as small as possible. … and _ff_ is as small as possible.
- **Ambiguity**: When several digit strings meet the condition, the last digit is left undetermined: implementation-defined or free per call is not said. The step's note is inexact: the criteria fix _k_ only, not _n_ or _s_ (radix 10, _x_ = 2<sup>-1073</sup>: 8e-324, 9e-324 and 1e-323 all meet them with _k_ = 1), so the choice is of _n_ and _s_.
- **Decision**: The integers are the implementation's function of the Number and the radix, the same at every call: the model's `numDigits`, read by the primitives NumberDigitsExponent, NumberDigitsCount and NumberDigitsSignificand, with the step's condition and _k_ least as its law (`Model.NumLaws.numDigits_least`); toExponential's step is the same function at radix 10. The engine takes, of the tuples with the least _k_, the one with _s_ × _radix_<sup>_n_ - _k_</sup> closest to ℝ(_x_), the even _s_ on a tie (the step's NOTE's rule). Nothing is asked of the host or logged.
- **Scope**: Number::toString and toExponential.

#### `performeval-substep-order`
- **Spec**: sec-performeval 12 (spec.html 30127)
- **Quote**: Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error detection:
- **Ambiguity**: The order of the substeps is implementation-defined.
- **Decision**: The written order; every order is observably the same.
- **Scope**: direct and indirect eval.

#### `parse-context`
- **Spec**: sec-parsetext 2 (spec.html 16439); sec-ParseJSON 3 (spec.html 47587); sec-performeval 12 (spec.html 30127); sec-scripts-static-semantics-early-errors (spec.html 26313-26328)
- **Quote**: Attempt to parse _sourceText_ using _goalSymbol_ as the goal symbol … unless the source text containing `super` is eval code that is being processed by a direct eval.
- **Ambiguity**: Early-error rules depend on "being parsed for ParseJSON", on eval's context and on whether the parse is of eval code being processed by a direct eval, which ParseText's signature does not carry.
- **Decision**: ParseText parses with no outside context; PerformEval and ParseJSON call ParseTextIn with theirs. ParseGoal and ParseTextIn carry _direct_, a Boolean; PerformEval passes whether its _direct_ is ~direct-eval~.
- **Scope**: eval and JSON.parse parsing.

#### `canonical-property-value-column`
- **Spec**: sec-runtime-semantics-unicodematchpropertyvalue-p-v 3 (spec.html 39060)
- **Quote**: Let _value_ be the canonical property value of _v_ as given in the “Canonical property value” column of the corresponding row.
- **Ambiguity**: "the canonical property value of _v_ as given in the “Canonical property value” column of the corresponding row": no table of the clause and no UCD file has a column of that name.
- **Decision**: The canonical property value is the long name of the PropertyValueAliases.txt row for _p_ that lists _v_ (CanonicalPropertyValue). No result depends on the choice: the value only feeds PropertyCharSet, which accepts any alias of it.
- **Scope**: UnicodeMatchPropertyValue, the \p{...} and \P{...} property escapes.

#### `hostloadimportedmodule-each-time`
- **Spec**: sec-HostLoadImportedModule (spec.html 29219-29237)
- **Quote**: then it must perform FinishLoadingImportedModule(_referrer_, _moduleRequest_, _payload_, _result_) with the same _result_ each time.
- **Ambiguity**: "each time" does not say whether it covers the calls made before the first one that performed a normal completion, which may have performed a throw completion.
- **Decision**: "each time" is every call: a host that once finishes a (referrer, request) pair with a normal completion finishes every call for an equal pair with that same result.
- **Scope**: HostLoadImportedModule's requirements, every host; the test host's module map (row test-host-module-loader).

#### `suspendthisagent-combined-suspend`
- **Spec**: sec-suspendthisagent 7 (spec.html 47050); sec-notifywaiter (spec.html 47056-47061)
- **Quote**: Perform LeaveCriticalSection(_waiterList_) and suspend the surrounding agent until the time is _waiterRecord_.[[TimeoutTime]], performing the combined operation in such a way that a notification that arrives after the critical section is exited but before the suspension takes effect is not lost. … another agent calling NotifyWaiter with arguments _waiterList_ and _thisAgent_ … _waiterRecord_: a Waiter Record,
- **Ambiguity**: Step 7 is one prose step for two operations, LeaveCriticalSection and a suspension the text does not define, performed as one so that no notification is lost; its wake condition calls NotifyWaiter with an agent signifier, whose second parameter is a Waiter Record (upstream #3328).
- **Decision**: Definition reading: LeaveCriticalSection(_waiterList_), then the host primitive SuspendAgentUntil(_waiterList_, _waiterRecord_.[[TimeoutTime]]), which carries the suspension, its atomicity with the LeaveCriticalSection before it, and the wake: by the timeout, or by NotifyWaiter(_waiterList_, _w_) for a Waiter Record _w_ whose [[AgentSignifier]] is the surrounding agent's (#3328 read as the Waiter Record of _thisAgent_). With one agent both readings of #3328 agree: nothing notifies, so the agent wakes only by the timeout.
- **Scope**: Atomics.wait in ~sync~ mode on an agent that can block (DoWait 28.a).

#### `notifywaiter-wake-agent`
- **Spec**: sec-notifywaiter 2.a (spec.html 47068); sec-suspendthisagent 7 (spec.html 47050)
- **Quote**: Wake the agent whose signifier is _waiterRecord_.[[AgentSignifier]] from suspension. … The surrounding agent can only wake from suspension due to a timeout or due to another agent calling NotifyWaiter
- **Ambiguity**: Step 2.a wakes another agent from a suspension the text does not define (SuspendThisAgent step 7's prose), so what the wake does, and how the suspended agent observes it, is not said.
- **Decision**: Definition reading: the host primitive WakeAgent(_waiterRecord_.[[AgentSignifier]]), logged. It wakes the agent of that signifier from its latest SuspendAgentUntil if it comes after it in the log, which AgentWoken reads, so a notification after the LeaveCriticalSection of step 7 is not lost. The suspended agent resumes in step 7's `Repeat, while AgentWoken() is *false*` loop, as 2.b's note says.
- **Scope**: Atomics.notify of a ~blocking~ waiter.

#### `b33-as-if-reparse`
- **Spec**: sec-functiondeclarations-in-ifstatement-statement-clauses (spec.html 54599)
- **Quote**: Source text matched by this production is processed as if each matching occurrence of |FunctionDeclaration[?Yield, ?Await, ~Default]| was the sole |StatementListItem| of a |BlockStatement| occupying that position in the source text.
- **Ambiguity**: "processed as if" is not defined: B.3.3 gives its |IfStatement| productions no rules of their own, and the text does not say which node the static and runtime semantics read in their place.
- **Decision**: A node of B.3.3's productions is processed as the |IfStatement| that a reparse of its source text with `{` before and `}` after each |FunctionDeclaration| child gives (the phrase "the |X| that {A} is processed as", CoveredBy's reparse): a new parser invocation in the node's context, once per node, its root's parent the node's parent. Rows on B.3.3's productions read that |IfStatement| for every SDO with a rule for |IfStatement| (Evaluation, HasCallInTailPosition, VarDeclaredNames, VarScopedDeclarations, ContainsDuplicateLabels, ContainsUndefinedBreakTarget, ContainsUndefinedContinueTarget) and for Contains; EarlyErrorsOf descends into it in place of the node's own children, and so does B.3.2's walk ("For each |FunctionDeclaration| _f_ that is directly contained in the |StatementList| of a |Block|, ...", ph-annexb-foreach), through ParseNodesWithinProcessed, so that it finds the |FunctionDeclaration| of `if (x) function f(){}` in the |StatementList| of the processed-as |Block|. ParseNodesWithin itself keeps the parse's own nodes; its other readers never meet the processed-as |IfStatement| or do not depend on it: ph-count-nodes-within/-before (CountLeftCapturingParensWithin/Before), ph-two-distinct (Pattern early errors), ph-contains-any-nt (RegExpBuiltinExec), CaptureGroupName, MightBothParticipate and GroupSpecifiersThatMatch walk a |Pattern|, whose grammar has no |Statement|; ph-node-within, ph-first/second-node-within, ph-contains-node, ph-not-contains-node and ph-not-contains-two-nodes in ParseTimeZoneOffsetString walk a |UTCOffset|-family parse (no |Statement|); ShallowestContainedJSONValue walks ParseJSON's |Script|, valid JSON text with no statement in it; ParenthesizedOperandIsError's first |CoverParenthesizedExpressionAndArrowParameterList| is its operand's unit chain, before any statement in preorder; Function.prototype.toString's readings (a |NativeFunction|) seek |PropertyName| and |NativeFunctionAccessor| and read only the source text they match, which the reparse, with only `{` `}` added around a |FunctionDeclaration|, leaves the same and in the same order. `LinEarly.linTree` likewise redirects B.3.3 `IfStatement` productions through `$CoveredBy(|IfStatement|, node)` inside reparsed covers.
- **Scope**: non-strict code under B.3.3 (the host is a web browser or otherwise supports it).

#### `agent-events-record-at-creation`
- **Spec**: sec-agent-clusters (spec.html 12507)
- **Quote**: Prior to any evaluation of any ECMAScript code by any agent in a cluster, the [[CandidateExecution]] field of the Agent Record for all agents in the cluster is set to the initial candidate execution.
- **Ambiguity**: The initial candidate execution has an Agent Events Record for each agent of the cluster, set before any agent evaluates code; the text does not say how an agent that a host creates while the cluster runs (test262's `$262.agent.start`) enters the cluster's candidate execution.
- **Decision**: A new agent's Agent Record shares the surrounding agent's [[CandidateExecution]], and its Agent Events Record (empty [[EventList]] and [[AgentSynchronizesWith]]) is appended to [[EventsRecords]] when the agent is created (`startBuiltin`), before it evaluates any code. The candidate execution then is the one the text's initial one would have become with that agent present from the start and idle until then: its Agent Events Record has no events either way, so no read, write or relation differs.
- **Scope**: agents created by the test host's `$262.agent.start`.

#### `job-agent-null-realm`
- **Spec**: sec-jobs (spec.html 12143); sec-hostenqueuepromisejob (spec.html 12299); sec-hostenqueuegenericjob (spec.html 12285)
- **Quote**: If a Realm Record is provided, these operations schedule the job to be performed at some future time in the provided realm, in the agent that owns the realm. If *null* is provided instead for the realm, then the job does not evaluate ECMAScript code. … It schedules _job_ to be performed at some future time. … in the agent signified by _realm_.[[AgentSignifier]]
- **Ambiguity**: A job is scheduled in an agent: the agent that owns its realm (the hooks with a realm say "the agent signified by _realm_.[[AgentSignifier]]"). HostEnqueuePromiseJob takes a _realm_ that may be *null* (NewPromiseReactionJob with an *undefined* handler) and names no agent, so which agent's job loop performs a job of no realm is not said.
- **Decision**: A job of realm *null* belongs to the agent that scheduled it, the surrounding agent of the HostEnqueuePromiseJob call; a job with a Realm Record belongs to the agent of its [[AgentSignifier]]. The reading is presupposed: the job settles a promise the scheduling agent's reaction holds, and "Jobs must run in the same order as the HostEnqueuePromiseJob invocations that scheduled them" orders it among that agent's promise jobs. With one agent every reading agrees.
- **Scope**: promise reaction jobs with an *undefined* handler in a test-host agent (`$262.agent.start`).

#### `agent-job-base-contexts`
- **Spec**: sec-jobs (spec.html 12146-12155)
- **Quote**: when there is no running context in the agent for which the job is scheduled and that agent's execution context stack is empty … Perform any host-defined cleanup steps, after which the execution context stack must be empty. … The Abstract Closure must return a normal completion, implementing its own handling of errors.
- **Ambiguity**: The test host performs an agent's jobs in AgentMain, the code of the agent's first execution context, so the agent's stack holds AgentMain's context and its realm's while its jobs run: it is not empty at a job's preparation nor after its cleanup. The text does not say how a host's agent other than the one it starts with runs its jobs.
- **Decision**: An agent's job is prepared on AgentMain's two contexts (`prepareJobOn` with base 2) and its cleanup leaves those two (`agentCleanupJob`, a stack of length 2). The difference is unobservable: neither context has a ScriptOrModule (AgentPrepareJob asserts it), so GetActiveScriptOrModule finds the job's own or none, as on an empty stack; a job's preparation pushes the context of its realm, and under a realm-*null* job the running realm is the agent's; no job's code reads a context below its own. As main's job loop does, AgentMain asserts that a job returns a normal completion: in checked mode, and in every mode at a job erratum's site (`Names.jobErrata`, by AgentJobClause). In an unchecked run an abrupt completion with no erratum is ignored, where main's loop ends with it.
- **Scope**: the jobs of agents created by the test host's `$262.agent.start`.

#### `tear-free-reads-aligned`
- **Spec**: sec-tear-free-aligned-reads 1.a.i (spec.html 53177)
- **Quote**: Assert: The remainder of dividing _readEvent_.[[ByteIndex]] by _readEvent_.[[ElementSize]] is 0.
- **Ambiguity**: Tear free reads is a condition on candidate executions, and its step 1.a.i is an Assert inside it: a failing Assert is a defect of the text, not an answer, so the step does not say whether an execution with an unaligned [[NoTear]] read has tear free reads.
- **Decision**: The memory model's meaning takes the Assert as a conjunct of the condition: an execution with a [[NoTear]] read whose [[ByteIndex]] is not a multiple of its [[ElementSize]] does not have tear free reads (Ecma.MemoryModel.TearFreeReads). The reading is presupposed: [[NoTear]] read events come from integer TypedArray element accesses, whose byte offset and index are multiples of the element size, so no reachable execution tells the readings apart. Law L2 (Ecma.Host.MemoryLaws.chooseReadsValid) takes the alignment of the read it appends as its premise (Ecma.MemoryModel.NewEvent.IsRead.aligned), and FastHost's proof of L2 takes it from there.
- **Scope**: the memory model; [[NoTear]] reads.

### Interpreting phrase meanings (11 entries)

#### `input-index-of`
- **Spec**: sec-regexpbuiltinexec 13.b (spec.html 39825)
- **Quote**: Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of _string_.
- **Ambiguity**: In Unicode mode _input_ is a List of code points, and the step does not say which character element _lastIndex_ of _string_ gives when _lastIndex_ is inside a surrogate pair or at the end of _string_.
- **Decision**: The index of the surrogate pair's character for a _lastIndex_ inside it, and the length of _input_ for _lastIndex_ = the length of _string_ (no element there).
- **Scope**: Unicode-mode RegExpBuiltinExec.

#### `split-code-units`
- **Spec**: sec-string.prototype.split (spec.html 36562); sec-regexpbuiltinexec (spec.html 39818)
- **Quote**: else let _input_ be a List whose elements are the code units that are the elements of _string_.
- **Ambiguity**: "a List consisting of the sequence of code units that are the elements of _head_" goes to CreateArrayFromList, whose argument is a List of ECMAScript language values; a code unit is not one.
- **Decision**: At RegExpBuiltinExec's _input_ the phrase is a List of the String's code units, in order. At split, the same phrase is the erratum SplitCodeUnitStrings (row split-code-unit-strings).
- **Scope**: RegExpBuiltinExec.

#### `error-object-terms`
- **Spec**: sec-throw-an-exception (spec.html 798); sec-parsetext (spec.html 16433)
- **Quote**: Return ThrowCompletion(a newly created *TypeError* object). … a non-empty List of *SyntaxError* objects
- **Ambiguity**: "a newly created *TypeError* object" names no realm and no creation steps; "a *SyntaxError* object" as a type is not defined.
- **Decision**: OrdinaryObjectCreate of the current realm's %NativeError.prototype% with an [[ErrorData]] slot holding undefined (no *"message"*); as a type, an object with an [[ErrorData]] slot, its prototype untested. An error the text creates has no own properties beyond the text's. This is a narrowing of §2's extensions (R10).
- **Scope**: every thrown error the text creates by that phrase; the *SyntaxError* type in signatures.

#### `charset-sort-ties`
- **Spec**: sec-compileatom (spec.html 38366); sec-compileatom (spec.html 38454)
- **Quote**: Sort _csSequences_ according to the length of each CharSetElement in descending order.
- **Ambiguity**: "Sort _csSequences_ according to the length of each CharSetElement in descending order" leaves the order of equal-length elements open.
- **Decision**: Equal lengths keep their order (a stable sort); two equal-length elements that both match leave the same MatchState, so the choice is not observable.
- **Scope**: `v`-mode class string disjunctions.

#### `contains-such-several`
- **Spec**: sec-privateelementfind (spec.html 6456); sec-InnerModuleLoading (spec.html 27382); sec-FinishLoadingImportedModule (spec.html 29262)
- **Quote**: contains a PrivateElement _entry_ such that _entry_.[[Key]] is _privateName_, then
- **Ambiguity**: "If _l_ contains a _T_ _x_ such that _c_, then … _x_" binds _x_ without saying which element when several satisfy _c_.
- **Decision**: With none the condition is false; with one, _x_ is it; with several the step stops (no pick).
- **Scope**: such conditions whose consequent reads the bound name.

#### `delete-derives-error`
- **Spec**: sec-delete-operator-static-semantics-early-errors (spec.html 20227)
- **Quote**: ultimately derives a phrase that, if used in place of |UnaryExpression|, would produce a Syntax Error according to these rules. This rule is recursively applied.
- **Ambiguity**: "ultimately derives a phrase that, if used in place of |UnaryExpression|, would produce a Syntax Error according to these rules" names no derivation; a cover derives many phrases.
- **Decision**: The phrase is the |Expression| of the |ParenthesizedExpression| the cover covers, through every nested parenthesization ("this rule is recursively applied"); the rules are the clause's two.
- **Scope**: `delete` of a parenthesized operand.

#### `registry-entry`
- **Spec**: sec-symbol.for (spec.html 31917); sec-keyforsymbol (spec.html 32158)
- **Quote**: Assert: _globalSymbolRegistry_ does not currently contain an entry for _stringKey_. … Assert: _globalSymbolRegistry_ does not currently contain an entry for _symbol_.
- **Ambiguity**: "does not currently contain an entry for _x_" is not defined for the GlobalSymbolRegistry List.
- **Decision**: An entry for a String is a Record whose [[Key]] is it; for a Symbol, one whose [[Symbol]] is it.
- **Scope**: those Asserts.

#### `has-attribute-values`
- **Spec**: sec-candeclareglobalfunction (spec.html 11358)
- **Quote**: _existingProperty_ has attribute values { [[Writable]]: *true*, [[Enumerable]]: *true* }
- **Ambiguity**: "has attribute values { [[Writable]]: *true*, [[Enumerable]]: *true* }" is not defined.
- **Decision**: Every attribute the Record lists is a field of the descriptor with the same value (SameValue); attributes it does not list are not tested.
- **Scope**: CanDeclareGlobalFunction.

#### `tobigint-boolean-literals`
- **Spec**: sec-tobigint (spec.html 5258-5264)
- **Quote**: Return `1n` if _primitive_ is *true* and `0n` if _primitive_ is *false*.
- **Ambiguity**: The Boolean row writes its results as source-text literals and its two cases as one sentence.
- **Decision**: The phrase "_a_ if _c_ and _b_ if _d_" reads the two cases.
- **Scope**: ToBigInt.

#### `annexb-replacing-early-errors`
- **Spec**: sec-functiondeclarationinstantiation 32.a.i.2 (spec.html 14018); sec-globaldeclarationinstantiation 12.b.ii.2 (spec.html 26533); sec-evaldeclarationinstantiation 13.b.ii (spec.html 30285)
- **Quote**: If replacing the |FunctionDeclaration| _funcDecl_ with a |VariableStatement| that has _funcName_ as a |BindingIdentifier| would not produce any Early Errors for _func_
- **Ambiguity**: The condition names a source transformation, not an operation, and "Early Errors for _func_" applies early error rules to a function object, not a Parse Node.
- **Decision**: The source text of the parse that made _funcDecl_ (through every cover), with _funcDecl_'s replaced by `var` _funcName_ `;`, parsed again with the same goal symbol and context; the condition holds when that parse succeeds and EarlyErrorsOf finds none in it. Early Errors for _func_ reads as _func_'s [[ECMAScriptCode]] with its [[FormalParameters]], the code of the function; the parse outside _body_, _script_ or that code is unchanged and had no early errors, so checking the whole parse is checking that code.
- **Scope**: Annex B.3.2's block-level function declarations in function, global and eval code.

#### `annexb-evaluated-in-place`
- **Spec**: sec-functiondeclarationinstantiation 32.a.i.2.c (spec.html 14024); sec-globaldeclarationinstantiation 12.b.ii.2.a.ii.3 (spec.html 26541); sec-evaldeclarationinstantiation 13.b.ii.7.b (spec.html 30314); sec-function-definitions-runtime-semantics-evaluation 1 (spec.html 24012-24016)
- **Quote**: When the |FunctionDeclaration| _funcDecl_ is evaluated, perform the following steps in place of the |FunctionDeclaration| Evaluation algorithm provided in
- **Ambiguity**: The step registers steps to run later, at another algorithm's evaluation of _funcDecl_, with no operation that does so: it does not say from when or for how long they replace FunctionDeclaration Evaluation, which variables they read, or what that Evaluation returns.
- **Decision**: The nested steps are an Abstract Closure with no parameters capturing the earlier variables they read (_funcName_), stored for _funcDecl_ by SetEvaluationSteps, a later such step for the same Parse Node replacing it. FunctionDeclaration Evaluation first asks EvaluationStepsOf(this Parse Node) and, when there are steps, calls them and returns their abrupt completion if they give one (as SortIndexedProperties' reading calls _sortCompare_); then its own step returns ~empty~. The steps return ~unused~ (spec.html 14029, 26893, 30635), which is not a completion value (UpdateEmpty, spec.html 4099, would keep it, and PerformEval, spec.html 30161, maps only ~empty~ to *undefined*), so the Evaluation they replace keeps its ~empty~.
- **Scope**: Annex B.3.2's block-level function declarations in function, global and eval code.

## 6. Model Choices (10 entries)

#### `promise-job-null-realm-code`
- **Spec**: sec-hostenqueuepromisejob (spec.html 12310)
- **Text / Context**: HostEnqueuePromiseJob's note says "When the _realm_ is *null*, no user ECMAScript code will be evaluated and no new ECMAScript objects (e.g. Error objects) will be created". NewPromiseReactionJob with an undefined handler still calls the derived promise's resolving functions, which are user code when a species constructor supplies them.
- **Model Decision**: Literal, with no stop, because a note states no requirement: an editorial report, not an erratum (nothing in the model reads the note). `Engine.Host.prepareJobOn` pushes an execution context for the agent's realm even when `_realm_` is `*null*` so user species resolving functions have a running execution context. The proposed reading changes the note.
- **Scope**: promise jobs of revoked-proxy or cross-realm handlers.

#### `ordinaryset-receiver-has-property`
- **Spec**: sec-ordinarysetwithowndescriptor 2.d.i (spec.html 13132)
- **Text / Context**: The Assert "_receiver_ does not currently have a property _propertyKey_" rests on the receiver's [[GetOwnProperty]] answer one step before. A Proxy receiver's trap may answer *undefined* for a configurable property of its extensible target: read on the receiver's own storage the Assert is vacuous for every Proxy, read through the Proxy it fails.
- **Model Decision**: Literal. The Assert has no checkable meaning (assert-provenance, permanent-sentences.txt), so a run passes it unchecked and does not stop under any reading: an editorial report, not an erratum. No reading looks through the Proxy.
- **Scope**: [[Set]] with a Proxy receiver whose getOwnPropertyDescriptor trap hides a target property.

#### `unicode-version`
- **Spec**: sec-string.prototype.normalize 7 (spec.html 36229)
- **Text / Context**: "the latest Unicode Standard" is an undated normative reference: the results change with Unicode releases.
- **Model Decision**: The model's Unicode data is the UCD release the pinned test262 expects (17.0.0, flake.nix's `ucd`), through UnicodeLaws.
- **Scope**: normalization, case mapping, property escapes, identifiers.

#### `sab-single-agent-reads`
- **Spec**: sec-getrawbytesfromsharedblock 6 (spec.html 45491); sec-getmodifysetvalueinbuffer 9.c (spec.html 45620); sec-atomiccompareexchangeinsharedblock 4 (spec.html 47216); sec-copydatablockbytes 6.a.iv (spec.html 4545)
- **Text / Context**: A read of a Shared Data Block takes "nondeterministically chosen byte values", constrained only by the memory model's valid-execution conditions. With one agent those conditions leave one value, the last write's bytes, so the readings restate the text there; the decision is the scope.
- **Model Decision**: With one Agent Events Record the four reads take the last write's bytes, the value the memory model forces. With several, the read is a scheduling point outside a critical section (AgentInterleave, where EnteredCriticalSections() is empty), then takes ChooseSharedBytes' bytes (overlay formal-choosesharedbytes): the host chooses the write event each byte reads from (ChooseReadsBytesFrom, row choose-reads-bytes-from), and the bytes are composed from those events as ComposeWriteEventBytes composes them, a ReadModifyWriteSharedMemory event's from its [[ChosenValue]] (valid chosen reads, spec.html 53136-53148).
- **Scope**: every cluster; Host.WF holds each host to law L1 (an event per byte, from the execution, writing that byte) and law L2 (chooseReadsValid: a valid execution whose memory order is the interleaving order stays valid with the read appended, reading the chosen events).

#### `annexb-module-reparse`
- **Spec**: sec-html-like-comments (spec.html 53808); sec-forbidden-extensions (spec.html 30005); sec-syntactic-grammar (spec.html 404)
- **Text / Context**: B.1.1 is "not allowed when parsing source text using the goal symbol |Module|", and a parse within a Module may have another goal: §5.1.5's cover and early-error reparses parse "the sequence of tokens originally matched", so the text's results are definite. The model reparses a node's source text, not tokens, which with B.1.1 on could read `<!--` as a comment where the Module's tokens were `<` `!` `--`.
- **Model Decision**: The model reparses a node's source text. The invocation's ParseCx.module (set when the goal is |Module|, inherited by a reparse of a node that invocation made: moduleParses, as strictParses) makes that reparse read B.1.1 as a reparse of the Module's tokens would: the grammar context's Ctx.module is it, so B.1.1's overlay is off there. Eval code and dynamic function text parse as Scripts.
- **Scope**: Annex B hosts; the lexical grammar of a Module and of the reparses within one.

#### `escape-pattern-same-invocation`
- **Spec**: sec-escaperegexppattern 5 (spec.html 39617-39641)
- **Text / Context**: "_escapedPattern_ may or may not differ from _pattern_; however, the Abstract Closure that would result from evaluating _escapedPattern_ as a _patternSymbol_ must behave identically to the Abstract Closure given by the constructed object's [[RegExpMatcher]] internal slot" does not say in which parser invocation _escapedPattern_ is parsed. In the model a Parse Node carries its invocation, so the separate-invocation reading is unsatisfiable: an escaped String's source text differs from _pattern_'s, and a program's CompilePattern can read the invocation.
- **Model Decision**: EscapePattern's String is compared as a |Pattern| parsed in _pattern_'s own invocation (`Host.WFIn.escapeBehaviour`). This is strictly weaker than the separate-invocation law, and the spec's CompilePattern reads no invocation. Hosts that answer _pattern_ itself meet it at every program.
- **Scope**: EscapePattern's behaviour law (`Host.WFIn`), every host.

#### `unchecked-asserts`
- **Spec**: sec-algorithm-conventions (spec.html 708)
- **Text / Context**: An Assert "asserts an invariant"; a prose Assert with no declared meaning cannot be checked.
- **Model Decision**: An Assert with no declared meaning is never checked, in any mode. permanent-sentences.txt lists those unchecked on purpose (future and provenance Asserts); asserts-open.txt lists the 6 that have no meaning yet.
- **Scope**: every run.

#### `canonical-carriers`
- **Spec**: sec-samevaluenonnumber 3 (spec.html 5745)
- **Text / Context**: The text's equality of values is by content (Strings by their code units, Lists by their elements), and the model's carriers are abstract.
- **Model Decision**: Lean `=` on a carrier is the text's equality (the laws eq_iff, str_ext, strEq_iff, seq_ext, symEq_iff, addrEq_iff and nodeEq_iff), so a model's carriers are canonical: a rope String, an unnormalized rational or a Seq with spare capacity is not a model. Fast (`Array`) and Ref (`List`) both meet it.
- **Scope**: every model (Ecma.Model.Laws).

#### `annexb-block-function-search-root`
- **Spec**: sec-functiondeclarationinstantiation (spec.html 14016); sec-globaldeclarationinstantiation (spec.html 26531); sec-evaldeclarationinstantiation (spec.html 30283)
- **Text / Context**: B.3.2's three block-function steps take "any |Block|, |CaseClause|, or |DefaultClause| _x_ such that _P_ Contains _x_ is *true*" (_P_ is _code_, _script_ or _body_). Contains walks only _P_'s own tree, so every _x_ the test admits is a node of that tree: searching the other trees made so far adds nothing.
- **Model Decision**: The step's phrase (ph-annexb-foreach) iterates ParseNodesWithin(_P_) in pre-order and keeps the Contains test, which drops nodes inside nested functions, classes' bodies and arrow functions. No primitive enumerates every parse tree. The machine reads only _P_'s tree, so it is preserved by State.Obs, which relates states only up to their live roots (World.keepRoots: dead and garbage stamps' records are ignored); a search over every recorded root would differ on related states.
- **Scope**: the three web-compat steps (the host is a web browser: --web-browser).

#### `annexb-block-function-arguments`
- **Spec**: sec-functiondeclarationinstantiation 22.f (spec.html 13978); sec-functiondeclarationinstantiation 32.a.i.2 (spec.html 14018); sec-functiondeclarationinstantiation 32.a.i.2.b (spec.html 14020)
- **Text / Context**: B.3.2.1's test is "_paramNames_ does not contain _funcName_", not _paramBindings_ (which adds "arguments" when an arguments object is made), so a block-level `function arguments() {}` in non-strict function code is hoisted: its evaluation sets the var-scoped "arguments" binding, replacing the arguments object. The text is definite, and upstream chose it (ecma262 #891, closing #815, kept _parameterNames_ here and added the `is not "arguments"` guard; #889's engine survey). test262's annexB/language/function-code/block-decl-func-skip-arguments.js expects the arguments object to stay: it was written to the text before #891 (its info quotes "Append "arguments" to parameterNames") and is stale (test262 #5113, PR #5112); staging/sm/lexical-environment/ block-scoped-functions-annex-b-arguments.js expects the function.
- **Model Decision**: The literal text: _paramNames_, no erratum. block-decl-func-skip-arguments.js is a known fail on every mode, not a finding: stage suite excludes it (tests/test262/suite.conf). The staging/sm test is a `pass` row of tests/test262/regress.txt, on the web-browser host.
- **Scope**: Annex B.3.2.1, a block-level FunctionDeclaration named `arguments` in non-strict function code (the host is a web browser: --web-browser).

## 7. Host-Choice Defaults (42 entries)
ECMA-262 leaves host hooks and implementation-defined choices abstract (`extern def`). SpecTec preserves those `extern def` interfaces untouched while `Engine/Host/` provides concrete test defaults:
- **`annexb-feature-choices`** (- host WebBrowser, - code Ecma.Host.OptionalLaws.webBrowser, - code Ecma.Host.OptionalLaws.webBrowserSupports, - code Grammar.AnnexB.Set, - code Engine.Host.annexBClauses, - code Engine.Host.HostOpts.annexB): Each feature is its own host choice, keyed by its clause: WebBrowser with `[.choice 0, .clause c]` ("the host is a web browser or otherwise supports c"), asked at the gated steps and early-error spans (B.3.1, B.3.2, B.3.4, B.3.6, B.3.9) and by the parser for each grammar overlay (B.1.1, B.1.2, B.3.3, B.3.5); `[.choice 1, .absent]` asks "the host is a web browser". Laws: an answer is fixed for a run, and every feature's answer is true where the host is a web browser. No law ties two features: on a host with B.3.3 and without B.3.2, B.3.3's synthetic Block is an ordinary Block, B.3.2's steps reading B.3.2's own answer. *(Spec: sec-additional-ecmascript-features-for-web-browsers (spec.html 53795-53797); sec-functiondeclarations-in-ifstatement-statement-clauses (spec.html 54599))*
- **`iso-year-form`** (- reading definition-sec-date.prototype.toisostring-7, - host ExpandedYearForm): The host's (ExpandedYearForm, a logged choice), asked only for a year in 0..9999; any other year is expanded. Every host's answer obeys Host.WF.expandedYearForm: a Boolean (or a stop), the state unchanged. The default hosts answer four digits, as test262 asks. *(Spec: sec-date.prototype.toisostring 7 (spec.html 35404); sec-date-time-string-format (spec.html 34450))*
- **`annex-b-web-browser`** (- silent EarlySentence.den, - silent choice (WebBrowser), - host WebBrowser): The default hosts (FastHost, RefHost) are not web browsers and otherwise support no Annex B feature: every step, early-error span and grammar overlay guarded by "the host is a web browser or otherwise supports …" takes the unsupported branch. `--web-browser` makes the test host a web browser (every feature supported) and `--annex-b <sec-id>` supports one feature. The normative optional built-in properties are still provided (normative-optional-properties): the default hosts support those, not Annex B's syntax and steps. Every host's answer obeys Host.WF.webBrowser: a Boolean (or a stop), the state unchanged, one Boolean for the same arguments in every state; which Boolean stays the host's. A host whose WebBrowser answers are false uses the default job callbacks (job-callback-hooks). *(Spec: sec-additional-ecmascript-features-for-web-browsers (spec.html 53793-54714); sec-web-scripting (spec.html 285-290))*
- **`normative-optional-properties`** (- host HostSupportsOptional, - host OmitSharedArrayBuffer): The default hosts provide every normative optional built-in property (HostSupportsOptional true; the realm's PropertyProvided) and keep *"SharedArrayBuffer"* (OmitSharedArrayBuffer false). *(Spec: sec-conformance (spec.html 239); sec-sharedarraybuffer-constructor (spec.html 45984))*
- **`property-order`** (- host PropertyOrder): The host's (PropertyOrder); the default hosts create them in document order, the order of their definitions in spec.html. *(Spec: sec-setdefaultglobalbindings 2 (spec.html 11873); sec-createintrinsics (spec.html 11847-11861))*
- **`forin-default-order`** (- host ForInStep): The default hosts' ForInStep follows CreateForInIterator's actions (sec-createforiniterator) while every action so far was its, else asks [[OwnPropertyKeys]] of the object (forInChoice). *(Spec: sec-enumerate-object-properties (spec.html 22771-22817))*
- **`date-parse-fallback`** (- host ParseDateString, - overlay formal-date.parse): Host.WF states every fixed part as a law of ParseDateString (HostLaws.lean): a time value, *NaN* or an integral Number within ±8.64 × 10^15, never -0𝔽 (parseDateString); a valid instance of the format by its fields and substitutes, date-only and offset forms as UTC less the offset (dateFormUTC), date-time forms without an offset as UTC of a local time (dateFormLocal), out-of-bounds element values and -000000 as *NaN* (dateFormIllegal); toISOString's String gives any time value (isoRoundTrip, from dateFormUTC). The round trips of toUTCString and toString are a "should" (spec.html 34795-34800), so a host feature, `Should.dateRoundTrip` (the host's `does`, fixed for the run): where it is true, for a time value with milliseconds 0, the Strings of toUTCString (utcStringRoundTrip) and of toString (DateString, TimeString, TimeZoneString; toStringRoundTrip) give it; where it is false, those Strings are as loose as other Strings. Both default hosts set it (their choice). Loose: other Strings (an integral in-range value or *NaN*), a day in (DaysInMonth, 31], `24` with nonzero `mm`, `ss` or `sss`, an offset `HH` of 24, and toString's String where the offset is not whole minutes under a day. Both default hosts' ParseDateString read with one parser over code units (`dateParse`, lean/Ecma/Host/DateLeaf.lean): the format (a local time as UTC; neither host has local time zone rules, so dateFormLocal is vacuous on both), toUTCString's and toString's forms with any offset and time zone name, else *NaN*. RefHost answers its value as a rational Number; FastHost as `numOf` of it where that reads back as it (`parseDateNum`; a binary64 holds every in-range integer, so this holds, but it is checked, not proved, and a failed check stops as residue). Date.parse is ToString of its argument, then ParseDateString (formal-date.parse), as the Date constructor's step 4.c.ii.2. *(Spec: sec-date.parse (spec.html 34791-34807); sec-date-time-string-format (spec.html 34439-34561); sec-expanded-years (spec.html 34563-34565))*
- **`native-function-source`** (- host NativeFunctionSource): The law asks for `function ` N `() { [native code] }` with N a name of the described form (empty, or `get `/`set ` or nothing, then an ASCII IdentifierName or `[Symbol.` one `]`), N = [[InitialName]] where that is a matched or empty String; that each such String has the NativeFunction syntax with N as its portion is stated over the grammar (NativeFormParses), not assumed. RefHost and FastHost answer N = [[InitialName]] where the form admits it, the empty N where [[InitialName]] is not a String, else residue; neither parses at run time. *(Spec: sec-function.prototype.tostring (spec.html 31662-31682))*
- **`native-function-source-form`** (- code Ecma.nativeName, - overlay prim-nativefunctionsource): A model choice, not a reading of the text: the host laws' NativeFunctionSource law admits only `function ` N `() { [native code] }`, N empty or, after `get `, `set ` or nothing, an ASCII IdentifierName without escapes or `[Symbol.` one `]`. A host answering another conforming String is not WF, and an [[InitialName]] matched by NativeFunctionAccessor? PropertyName that is not such an N has no answer the law admits (residue). Conformance does not need the narrowing; it is kept for proof cost. The steps run as written. *(Spec: sec-function.prototype.tostring 3 (spec.html 31669))*
- **`escape-pattern`** (- host EscapePattern): RefHost: *"(?:)"* for the empty pattern, else the minimal escape of `/` and line terminators; FastHost: the pattern itself where it needs no escape (non-empty, no unescaped `/`, no line terminator) and *"/"*, it, *"/"* and the flags parse as a |RegularExpressionLiteral| whose body it is; else RefHost's answer where that is such a body and a runtime check finds its |Pattern| (the flags' parameters) in every grammar context, strict or not, under both grammar readings (`patternAt`), for the empty pattern also each |Pattern| tree of it and of *"(?:)"* the one `empty_sim` takes (`emptyShapes`); else it stops (residue). The check proves FastHost's `Host.WF` unconditionally. At the spec's program the behaviour law holds for the empty pattern (`escapeSim_spec`, by `empty_sim`), and for the others under the named hypothesis `EscapeSimText` of `wfIn_spec` and `wfInBy_spec` (`escape_sim_spec` needs StepGaps, false at text-changing escapes until StepGaps.phCall is restated). `Host.WFIn.escapeBehaviour` quantifies over a `rer` that is a Record of the six RegExp Record fields, its five flags Booleans (`RerFields`, `RerFlags`), with `rer`, `input` and the cells they reach allocated (`ReachAlloc`): *"(?:)"*'s CompileAtom reads the flags (UpdateModifiers) and the empty pattern's does not, and a dangling `input` stops one but not the other; the patterns are evaluated as RegExp objects, whose [[RegExpRecord]] has every field, the flags Booleans (RegExpInitialize), and whose matcher RegExpBuiltinExec calls on a fresh List. *(Spec: sec-escaperegexppattern 4-5 (spec.html 39617-39641); sec-updatemodifiers (spec.html 38586); sec-regexpinitialize 19 (spec.html 39167); sec-regexpbuiltinexec 11 (spec.html 39818))*
- **`host-defined-operations`** (- silent knotCall): An algorithm the data has no body for is a host hook; an unknown clause stops as residue. *(Spec: sec-hosts-and-implementations (spec.html 303); sec-host-hooks-summary (spec.html 54778))*
- **`resizable-buffers`** (- silent hooks (HostResizeArrayBuffer), - silent hooks (HostGrowSharedArrayBuffer)): ~unhandled~: the spec's own steps resize. *(Spec: sec-hostresizearraybuffer (spec.html 45340-45359); sec-hostgrowsharedarraybuffer (spec.html 45947-45970))*
- **`math-random`** (- silent hooks (Math.random)): +0, a test host's answer (the seeded host: a multiple of 2^-53 drawn from its seed, other than ½), except ½ at the Realm's call numbered one past the log position of its first call (`realmMark`): distinct Realms have distinct first positions, so their sequences differ there. *(Spec: sec-math.random (spec.html 33593-33597))*
- **`locale-sensitive-methods`** (- host LocaleUppercase, - host LocaleLowercase, - host LocaleCompare, - host LocaleNumberString, - host LocaleDateString, - reading definition-sec-string.prototype.localecompare-4, - overlay formal-string.prototype.tolocaleuppercase, - overlay formal-string.prototype.tolocalelowercase, - overlay formal-number.prototype.tolocalestring, - overlay formal-bigint.prototype.tolocalestring, - overlay formal-date.prototype.tolocalestring, - overlay formal-date.prototype.tolocaledatestring, - overlay formal-date.prototype.tolocaletimestring, - overlay formal-%typedarray%.prototype.tolocalestring): Host choices (LocaleUppercase, LocaleLowercase, LocaleCompare, LocaleNumberString, LocaleDateString; laws Host.WF.localeCase, localeCompare, localeNumberString, localeDateString). LocaleDateString gives a String or ~empty~ (the non-locale form: toDateString's, toTimeString's or toString's) for an object with a [[DateValue]] slot, and a String or ~throw~ (a *TypeError*) for any other *this* value: the reading of "not generic" that every algorithmic Date method follows, as a bound (D3). Loose: the case mappings' locale exceptions, the comparison's order and magnitude, every String's contents, and whether a non-Date *this* gives a TypeError or a String. The test hosts answer as a locale with no rules of its own: toUppercase and toLowercase, -1, +0 or 1 by the code point order of the canonical decompositions (NFD), ~empty~ (toString's String), and for Date ~empty~ (the forms of toDateString, toTimeString and toString, in UTC: row time-zones) and ~throw~ for a non-Date *this*. %TypedArray%.prototype.toLocaleString is an overlay algorithm: those steps, with the host choice ListSeparator (row other-host-choices) as the separator; the clause's optimisation sentence is advice. ECMA-402 itself stays outside the base layer (scope). *(Spec: sec-string.prototype.tolocaleuppercase (spec.html 36646-36655); sec-string.prototype.tolocalelowercase (spec.html 36635-36644); sec-string.prototype.localecompare (spec.html 36128-36173); sec-number.prototype.tolocalestring (spec.html 32833-32838); sec-bigint.prototype.tolocalestring (spec.html 33334-33339); sec-date.prototype.tolocaledatestring (spec.html 35426-35431); sec-date.prototype.tolocalestring (spec.html 35433-35438); sec-date.prototype.tolocaletimestring (spec.html 35440-35445); sec-properties-of-the-date-prototype-object (spec.html 34845); sec-%typedarray%.prototype.tolocalestring (spec.html 42881-42892))*
- **`execution-resources`** (- host DiscardContextResources): Resources are a host feature. A host may stop a run at an implementation limit (implLimit) only when it pushes an execution context while the contexts on the stack whose resources were not discarded (DiscardContextResources) exceed a bound fixed for that host (Host.exhausts; law Host.WF.contextResources, over liveContexts). A chain of tail calls does not raise that count, so its length never reaches the limit. It may also stop a run at an implementation limit when it allocates an object (MakeBasicObject's MakeObject) while the allocated heap cells exceed a bound fixed for that host (Host.exhaustsHeap, read with Host.allocL; law Host.WF.heapResources, over CellsAbove): the embedding's termination of a runaway agent (spec.html 12496-12498). Mid-job termination happens only at such a push or allocation. Loose: the bounds. Termination between jobs is the host's next-job answer none: the job loop logs it as `next none` only where every Job scheduled (a hook whose first argument is an Abstract Closure: generic, promise and timeout jobs; cleanup jobs run "if possible") has been taken (`drained`), else as `terminate`, the embedding's termination of the agent (`nextCall`). The test hosts have no bound (exhausts and exhaustsHeap are false). *(Spec: sec-preparefortailcall (spec.html 26268-26281); sec-agent-clusters (spec.html 12496-12498); sec-ecmascript-function-objects-call-thisargument-argumentslist 7 (spec.html 13508))*
- **`time-zones`** (- silent hooks (GetNamedTimeZoneOffsetNanoseconds), - silent choice (time zones), - silent choice (TimeZoneNameSuffix), - silent choice (SystemTimeZoneString), - host SupportsOnlyUTC, - host HasTimeZoneRules, - host AvailableNamedTimeZoneIds, - host IsNonPrimaryTimeZoneId, - host LastTransitionBefore, - host TimeZoneNameSuffix, - host SystemTimeZoneString): UTC only: offset 0, no local political rules, the one identifier *"UTC"* and no non-primary ones, no transitions, system zone "UTC", empty name suffix. *(Spec: sec-getnamedtimezoneoffsetnanoseconds (spec.html 34142-34160); sec-availablenamedtimezoneidentifiers (spec.html 34192-34220); sec-systemtimezoneidentifier (spec.html 34222-34244))*
- **`jobs`** (- silent hooks (job enqueue), - silent nextJob, - silent prepareJob, - silent inJob, - silent program): The enqueue call is the queue entry; generic and promise jobs in scheduling order, then timeout jobs (one due at or past the time value limit stops at the implementation limit: test-host-clock); a null-realm job pushes the agent's realm context (`Engine.Host.prepareJobOn`); a top-level abrupt completion ends the run before queued jobs. *(Spec: sec-jobs (spec.html 12140-12328); sec-runtime-semantics-scriptevaluation (spec.html 26446-26477))*
- **`approximations`** (- silent choice (Approx), - silent choice (ApproxInteger), - silent choice (HostChoice), - host Approx, - host ApproxInteger, - host HostChoice): The exact value converted with 𝔽 (FastHost; RefHost's stops); an integer itself; of two Strings the second, else the first. *(Spec: sec-hosts-and-implementations (spec.html 296); sec-function-properties-of-the-math-object (spec.html 33173); sec-setfunctionname (spec.html 13851))*
- **`other-host-choices`** (- silent choice (HostInitializeBuiltinContext), - silent choice (AdditionalTimeout), - silent choice (SpinWaitHint, DiscardContextResources), - silent choice (CanAllocate), - silent choice (DebuggerEnabled), - silent choice (HostGlobalObject, HostThisValue, MayCleanup), - silent choice (HostReportCleanupError), - host HostInitializeBuiltinContext, - host AdditionalTimeout, - host SpinWaitHint, - host CanAllocate, - host DebuggerEnabled, - host DebuggerAction, - host HostGlobalObject, - host HostThisValue, - host MayCleanup, - host HostReportCleanupError): ", " separator; no added timeout; no pause or resource hint; allocation up to 2^32 bytes; no debugger (RefHost's DebuggerAction does nothing); ~empty~ global object, this value and cleanup cell; no built-in context initialization (the global properties: test-host-global-properties). *(Spec: sec-localizedlistseparator (spec.html 41501-41507); sec-dowait (spec.html 47153); sec-atomics.pause (spec.html 47446-47462); sec-createbytedatablock (spec.html 4486-4500); sec-debugger-statement-runtime-semantics-evaluation (spec.html 23518-23530); sec-initializehostdefinedrealm (spec.html 11816-11845))*
- **`test-host-global-properties`** (- silent choice (HostGlobalProperties), - host HostGlobalProperties): The test host's HostGlobalProperties (FastHost.globalProps) adds `print` (writable, enumerable, configurable) and `$262` (writable, configurable) to _global_ where it has no property of that key. Each function is a new built-in function object made like the realm's %isNaN% (its slots, [[Behaviour]] the host's algorithm, *"length"* 1, *"name"* its name); `$262` is a new object made like %Reflect%, with *"global"* (_global_), *"detachArrayBuffer"*, whose algorithm throws a *TypeError* for a non-ArrayBuffer or a SharedArrayBuffer, then performs DetachArrayBuffer(_buffer_) and returns *null*, and *"createRealm"* (*"length"* 0), whose algorithm (FastHost.createRealmBuiltin) performs InitializeHostDefinedRealm(), removes the execution context it pushed and restores the caller's as the running one, then returns ? Get(_realm_.[[GlobalObject]], *"$262"*) of the new realm, whose `$262` comes from this same step 17; the well-known symbols and the Agent Record (its [[GlobalSymbolRegistry]]) are shared, and *"evalScript"* (FastHost.evalScriptBuiltin), which throws a *TypeError* for a non-String (INTERPRETING.md asks only for a String), then performs ParseScript(_sourceText_, the current Realm Record, *undefined*), returns a throw completion of the first error of a List of errors, else Completion(ScriptEvaluation(_s_)); *"IsHTMLDDA"* where the host supports §B.3.6 (test-host-is-html-dda). The law (Host.WF.hostGlobalProperties): only _global_'s own properties change, its slots kept, and new cells may be made. RefHost adds nothing. *(Spec: sec-initializehostdefinedrealm 17 (spec.html 11842); sec-detacharraybuffer (spec.html 45275); sec-initializehostdefinedrealm (spec.html 11816-11845); sec-parse-script (spec.html 26423-26444); sec-runtime-semantics-scriptevaluation (spec.html 26446-26469))*
- **`test-host-is-html-dda`** (- host HostGlobalProperties, - code Engine.Host.htmlDDA, - code Engine.Host.ddaProps, - code Engine.Host.isHTMLDDABuiltin, - code Engine.Host.ddaBy): Where the host is a web browser or otherwise supports §B.3.6 (`--web-browser`, `--annex-b sec-IsHTMLDDA-internal-slot`: FastHost.ddaBy), HostGlobalProperties gives `$262` *"IsHTMLDDA"* (writable, configurable) in every realm, `$262.createRealm()`'s included: a new built-in function object made like the realm's %isNaN% with an [[IsHTMLDDA]] internal slot (*undefined*), *"length"* 0 and *"name"* *"IsHTMLDDA"* (FastHost.htmlDDA), whose algorithm (FastHost.isHTMLDDABuiltin) returns *null* for every argument list. Its internal methods are a built-in function's, so it is not exotic. Elsewhere `$262` has no *"IsHTMLDDA"*. *(Spec: sec-IsHTMLDDA-internal-slot (spec.html 54681-54693); sec-initializehostdefinedrealm 17 (spec.html 11842))*
- **`test-host-module-loader`** (- file spec/formal/host.emu, - silent hooks (HostGetSupportedImportAttributes)): The test host's HostGetSupportedImportAttributes answers « *"type"* ». Its HostLoadImportedModule is a host algorithm (Spec.Host.hostProg): the key is the specifier and the *"type"* attribute's value, or ~empty~ for none (any referrer); a key mapped before gives its Module Record (the map is the host-call log, its earliest entry); else the run's module sources (ecma-run --module-dir: each `*_FIXTURE.js` and `*_FIXTURE.json`, and each `.js` or `.json` file there that the program or a module it reaches names, as `./NAME`, per test262 INTERPRETING.md) give, for *"json"*, Completion(ParseJSONModule(source)), its normal value added to the map; for another type, a throw completion of a new *TypeError*; for none, ParseModule's record in the current Realm, added to the map, or a throw completion of its first SyntaxError. A specifier with no source is a throw completion of a new *TypeError*. FinishLoadingImportedModule follows synchronously. *(Spec: sec-HostLoadImportedModule (spec.html 29219-29237); sec-hostgetsupportedimportattributes (spec.html 29292-29306))*
- **`test-host-module-run`** (- file spec/formal/host.emu, - code Engine.Host.Source.module): The test host's module run (ecma-run --module, `Engine.Host.Source.module`): ParseModule in the host's Realm (its first error a throw completion); HostModuleLoaded(`./NAME`, the record), so that the root imports itself by its file name; LoadRequestedModules, whose promise is settled when it returns (the loader is synchronous; a rejection is a throw completion of its reason); Link (an abrupt completion ends the run); Evaluate; then the queued jobs. The outcome is Evaluate's promise's: rejected, a throw of its reason; fulfilled, *undefined*; pending, the promise. `--parse-only` runs ParseModule alone (test262's `parse` negative module tests). *(Spec: sec-example-cyclic-module-record-graphs (spec.html 27751-27755); sec-moduleevaluation (spec.html 27497-27498))*
- **`test-host-clock`** (- silent choice (TimeNow), - silent nextJob, - host TimeNow): The default test hosts' clock (FastHost, RefHost, `clockAt`): 1 ms at the first reading, 1 ms more at each later one; taking a job moves it to at least the job's due time (the time at its HostEnqueueTimeoutJob call plus _milliseconds_ rounded up, `dueAt`), so each later reading is past it; never back, at most the time value limit. FastHost stops at the implementation limit (`Stop.implLimit`) where the job it takes is due at or past the limit. The test hosts' elapsed time is that clock's as they take a job (`clockElapsed`), and their next job is checked against the laws (`checkElapsed`, else the implementation limit). Every test host's TimeNow is `readClock`, which also stops at the implementation limit where a reading is below a taken timeout job's due time. The seeded clock (--host-seed) is `timeAt`, about 1 s a host call, plus the default clock's time, so a taken job moves it to at least its due time too; its job order is its own, and it never takes a timeout job due past the limit from its call's `timeAt`, so the run ends with that job pending. A busy-wait on Date.now ends. *(Spec: sec-date.now (spec.html 34786-34789); sec-date (spec.html 34741-34745); sec-dowait (spec.html 47152); sec-hostenqueuetimeoutjob (spec.html 12324); sec-time-values-and-time-range (spec.html 33769))*
- **`nan-encoding`** (- reading definition-sec-numerictorawbytes-1.a, - reading definition-sec-numerictorawbytes-2.a, - reading definition-sec-numerictorawbytes-3.a, - silent choice (NaNEncoding), - host NaNEncoding): One host-chosen encoding per format (NaNEncoding), the same each time; the default host's is the canonical quiet NaN. *(Spec: sec-numerictorawbytes 1.a-3.a (spec.html 45543-45547))*
- **`host-choices-without-laws`** (- reading definition-sec-cleanup-finalization-registry-3, - reading definition-sec-debugger-statement-runtime-semantics-evaluation-1, - reading definition-sec-host-cleanup-finalization-registry-2, - code Ecma.objKept, - code Ecma.Host.OptionalLaws.debuggerAction): A host step keeps to a frame stricter than §6.1.7.3: it changes only the heap, each object as §6.1.7.3 allows and no other internal slot or cell. Every internal slot but [[Extensible]] and [[Prototype]] stays as it was (`objKept`), and every cell that is not an object or a property's attribute Record (Lists, Data Blocks, Environment Records) stays as it was (`heapKept`), but for the cells and slots a host-defined operation is given to change (`hookFree`, `hookSlots`). It binds the host-defined operations (`hookFrame`), the host choices without a law of their own on the state, HostReportCleanupError among them (`choiceFrame`), the job steps (`nextJobFrame`, `clearsKeptFrame`, `prepareJobFrame`, `cleanupJobFrame`), and DebuggerAction at its objects (`debuggerAction`). A host keeps its own state outside the model's State. MayCleanup's entry returns to readings-restating.txt with C1. *(Spec: sec-invariants-of-the-essential-internal-methods (spec.html 2911); sec-cleanup-finalization-registry 3-3.a (spec.html 12699-12700); sec-debugger-statement-runtime-semantics-evaluation 1-1.a (spec.html 23525-23526); sec-host-cleanup-finalization-registry 2 (spec.html 12649))*
- **`agent-record-choices`** (- code Engine.Host.newAgent, - code Ecma.Host.ChangeLaws.agentFixed): The driver builds the Agent Record before the machine runs (newAgent). Two laws hold it to Table 29: AgentRecordOk gives the initial values and one Agent Events Record whose [[AgentSignifier]] is [[Signifier]] (init_agentOk proves it of the Fast host's init), and Host.WF.agentFixed keeps the fields that cannot change, and [[GlobalSymbolRegistry]], across every host step. [[LittleEndian]], [[CanBlock]] and [[IsLockFreeN]] stay open host choices: the test hosts answer [[LittleEndian]] true, [[CanBlock]] false and every [[IsLockFreeN]] true, for the whole run. *(Spec: sec-agents (spec.html 12350-12407))*
- **`suspend-agent-until`** (- host SuspendAgentUntil, - code Ecma.suspendUntil, - code Ecma.Clock.step, - code Engine.Host.HostOpts.canBlock): The default test hosts' surrounding agent cannot block (DoWait 12 throws), unless the run asks (`--can-block`, which test262-runner passes for a CanBlockIsTrue test). SuspendAgentUntil only registers the suspension: on the default test hosts (FastHost, RefHost, `suspendUntil`) it answers ~unused~ with the state unchanged, on a time or +∞, and the logged call is the suspension that AgentWoken, AgentTimeout and HostSelectAgent read (`pendingAt`). The wait is step 7's AgentInterleave loop. The default clock (`Clock.step`) moves at AgentTimeout, to at least its answer rounded up to a millisecond (row agent-timeout), and by 1 ms at each selection of an agent, so a later Date.now is not before a wake; the seeded clock (--host-seed) adds the default clock's time, so a wake moves it too.  Note that `wakeFinite` (`16-host-laws-jobs.spectec`) treats finite suspension timeouts past `maxTime` (8.64 × 10^15 ms) as never waking by timeout. *(Spec: sec-suspendthisagent 7 (spec.html 47050); sec-agentcansuspend (spec.html 12430-12437); sec-dowait 12 (spec.html 47128))*
- **`agent-interleaving`** (- overlay formal-agent-interleave, - code Ecma.Prims.Context.switchToAgent): The agents of a cluster share one executing thread and switch cooperatively, only at AgentInterleave (overlay formal-agent-interleave): the host's HostSelectAgent picks the agent that runs next, SwitchToAgent parks the surrounding agent's execution context stack in its [[ParkedStack]] and installs the target's, and a Resume continues the target where it last switched. AgentInterleave is performed at SuspendThisAgent step 7's wait loop and at the four shared reads with several Agent Events Records (sab-single-agent-reads), never inside a critical section, so AcquireCriticalSection's one-agent meaning stays exact; the other scheduling points (the $262.agent functions, main's idle loop) come with a multi-agent host. With sequentially consistent shared reads, every finer interleaving is observably the same, except that an agent looping forever with no scheduling point starves the others: the run stops out of fuel where the text's forward progress would let them finish. *(Spec: sec-forward-progress (spec.html 12518-12528))*
- **`agent-fairness`** (- host HostSelectAgent, - code Ecma.selectNext, - code Ecma.switchable, - code Ecma.Host.JobLaws.selectAgent): Host.WF's selectAgent row holds every host to a per-call law: ~empty~, or an Agent Record whose [[Signifier]] is one of the cluster's [[AgentSignifier]]s and not the surrounding agent's, other than the surrounding agent, that can run. Suspensions are keyed by Agent Record and wakes by signifier, so the law needs no relation between an agent's signifier and its Record (sorts: the signifier is opaque); with AgentTimeout it gives the text's one-agent progress. FastHost's HostSelectAgent is round-robin over the cluster's [[EventsRecords]] order after the surrounding agent's signifier (selectNext; its signifiers are its Agent Records), and proves the stronger per-call law selectNext_fair: it passes over only agents it cannot switch to (`switchable`), and answers ~empty~ only where it can switch to none. Since SwitchToAgent installs the selected agent, an agent that can run at each of B consecutive selections, B the cluster's size, is selected among them. Bounded fairness is FastHost's choice, not a Host.WF row: RefHost has one agent and answers ~empty~. *(Spec: sec-forward-progress (spec.html 12518-12528))*
- **`choose-reads-bytes-from`** (- host ChooseReadsBytesFrom, - code Ecma.scWrites, - code Ecma.Host.MemoryLaws.chooseReadsBytesFrom, - code Ecma.Host.MemoryLaws.chooseReadsValid, - overlay formal-choosesharedbytes): ChooseReadsBytesFrom is the host's choice of a read's reads-bytes-from: a List of _elementSize_ write events, one per byte. Host.WF's chooseReadsBytesFrom (law L1) holds every host to a new List of that length whose element j is an event of the execution's [[EventList]]s that writes byte _byteIndex_ + j of the block. FastHost answers the sequentially consistent execution (scWrites): each byte's latest write in the interleaving order, rebuilt from the log's HostSelectAgent cuts (each logged _n_ ends an agent's segment of its [[EventList]]); a byte no event wrote is residue. RefHost has one agent and answers residue. *(Spec: sec-reads-bytes-from (spec.html 53041-53046); sec-valid-chosen-reads (spec.html 53138-53149))*
- **`agent-timeout`** (- host AgentTimeout, - code Ecma.agentTimeout, - code Ecma.agentTimeout): AgentInterleave performs the host primitive AgentTimeout where HostSelectAgent answers ~empty~. The default test hosts (FastHost, RefHost, `agentTimeout`) answer the time now where the surrounding agent can run, else the earliest wake by a timeout of the Agent Records suspended in the log (`suspendedAgents`), not before now; the default clock (`Clock.step`) moves to that time rounded up to a millisecond. Where no agent wakes by a timeout (+∞, or past the last time value) it stops out of fuel.  *(Spec: sec-suspendthisagent 7 (spec.html 47050); sec-forward-progress (spec.html 12518-12528))*
- **`agent-woken`** (- host AgentWoken, - code Ecma.agentWoken, - code Ecma.agentWoken): Step 7's loop asks the host primitive AgentWoken. The default test hosts (FastHost, RefHost, `agentWoken`) answer whether the surrounding agent can run (`runnable`): *true* once a WakeAgent of its signifier follows its latest SuspendAgentUntil in the log, or the clock has reached its timeout; never a spurious wake.  *(Spec: sec-suspendthisagent 7 (spec.html 47050))*
- **`wake-agent`** (- host WakeAgent, - code Ecma.pendingIn): The host primitive WakeAgent answers ~unused~ and leaves the state as it is on the default test hosts (FastHost, RefHost): the wake is the logged call itself, which AgentWoken and HostSelectAgent read (`pendingIn`).  *(Spec: sec-notifywaiter 2.a (spec.html 47068))*
- **`annexb-block-function-hoisting-domain`** (- overlay ph-annexb-foreach, - overlay formal-directlycontaininglist, - code Ecma.Prims.Nodes.instanceOf): The step is a For-each over the List its phrase (ph-annexb-foreach) gives. A node is directly contained in a list nonterminal's instance when every node between them has a single child node (FunctionDeclaration through HoistableDeclaration, Declaration and StatementListItem; not through a LabelledStatement or another statement), the list taken at the outermost of its own recursion (DirectlyContainingList). _x_ ranges over ParseNodesWithin(_P_), the only nodes _P_ Contains reaches (annexb-block-function-search-root); the declarations come in source text order. "_child_ is an instance of _x_" for a Parse Node _x_ is "_child_ is _x_", so _P_ Contains _x_ holds when Contains's walk reaches _x_ (not into nested functions, classes' bodies or arrow functions). *(Spec: sec-functiondeclarationinstantiation (spec.html 14016); sec-globaldeclarationinstantiation (spec.html 26531); sec-evaldeclarationinstantiation (spec.html 30283); sec-static-semantics-contains (spec.html 9474-9482))*
- **`host-extension-hooks`** (- reading definition-sec-initializehostdefinedrealm-2, - reading definition-sec-error-message-5, - reading definition-sec-nativeerror-5, - reading definition-sec-aggregate-error-7, - reading definition-sec-suppressederror-6, - host HostExtendIntrinsics, - host HostExtendObject, - code Ecma.onlyAdds, - code Ecma.noForbiddenProps): Two host hooks. HostExtendIntrinsics(_realm_) runs right after CreateIntrinsics in InitializeHostDefinedRealm; HostExtendObject(_o_) runs on each error object the machine creates, before the Error, _NativeError_, AggregateError and SuppressedError constructors return it and in "a newly created _name_ object" (ph-new-error). Their laws (Host.WF.hostExtendIntrinsics, Host.WF.hostExtendObject): the answer is ~unused~; only own properties are added (to any object, or only to _o_), no internal slot, existing property or other cell changes, new cells may be made (onlyAdds); no new own *"caller"* or *"arguments"* on an object with a [[Call]] (noForbiddenProps). The test hosts (FastHost, RefHost) add nothing and leave the state as it is. *(Spec: sec-conformance (spec.html 235); sec-error-handling-and-language-extensions (spec.html 29969); sec-forbidden-extensions (spec.html 29973-30012); sec-initializehostdefinedrealm 2 (spec.html 11822); sec-error-message 5 (spec.html 32190); sec-nativeerror 5 (spec.html 32331); sec-aggregate-error 7 (spec.html 32719); sec-suppressederror 6 (spec.html 32485))*
- **`job-callback-hooks`** (- reading definition-sec-hostmakejobcallback-1, - reading definition-sec-hostcalljobcallback-2, - host HostJobCallbackData, - host HostPrepareCallJobCallback, - host HostCleanupCallJobCallback, - code Ecma.Host.JobLaws.jobCallbackDefault): Readings make the host's parts host primitives and keep the requirements by construction: HostMakeJobCallback returns { [[Callback]]: _callback_, [[HostDefined]]: HostJobCallbackData(_callback_) }; HostCallJobCallback performs HostPrepareCallJobCallback(_jobCallback_), then Completion(Call(…)), then HostCleanupCallJobCallback(_jobCallback_), and returns ? the Call's completion. Laws: HostJobCallbackData keeps to choiceFrame; the two bracket steps give ~unused~ and change only the heap, the execution context stack and the suspended context (Host.WF.callJobCallbackFrame, jobFrame); where every WebBrowser answer in the log is false, HostJobCallbackData gives ~empty~ and the bracket steps ~unused~, each leaving the state as it is: the default implementations (Host.WF.jobCallbackDefault). The test hosts (FastHost, RefHost, the legacy diff host) answer the defaults for every run, web browser or not. *(Spec: sec-hostmakejobcallback (spec.html 12239-12245); sec-hostcalljobcallback (spec.html 12263-12273))*
- **`weakref-collection`** (- code Ecma.Host.collect, - code Ecma.Host.ChangeLaws.collect, - code Ecma.Collected, - code Ecma.collectBoundary): At a job boundary, after ClearKeptObjects, where `drive` holds no saved computation (State.saved 0), the host's step `collect` runs, logged: it gives a set of objects and Symbols and empties every WeakRef and FinalizationRegistry cell whose [[WeakRefTarget]] is one of them, together, nothing else changing. The law (Host.WF.collect, Collected): no element is reachable from the roots (the execution context stack, the resumed and suspended values, the Agent Record with its [[KeptAlive]], the bookkeeping, the host-call log's values: the scheduled jobs and the realms, the WaiterList Records and Shared Data Blocks), counting every cell value but a [[WeakRefTarget]] whose target is in the set itself (a WeakRef's edge to a value outside the set keeps it); reachability is a sound under-approximation of non-liveness. MayCleanup then has emptied cells to give. Loose: collection at other times (within a job, or while a computation is saved, whose Lean locals are not roots); a WeakMap's or WeakSet's entries (their keys count as reachable, so no entry is ever emptied); the _enqueueCleanup_ choice (no cleanup job is enqueued); sets beyond the reachable bound. The test hosts collect nothing (the default `Host.collect`). *(Spec: sec-weakref-execution (spec.html 12603-12631))*
- **`parsejson-result-defined-by`** (- reading definition-sec-ParseJSON-8): The checked Assert reads it as: if _result_ is an Object, _script_ Contains |ArrayLiteral| or |ObjectLiteral|; otherwise _result_ is a String, a Number, a Boolean or *null*. The only Object a valid JSON text's |Expression| has as its value is the one its outermost |ArrayLiteral| or |ObjectLiteral| creates, so the reading holds wherever the text's does. *(Spec: sec-ParseJSON 8 (spec.html 47592))*
- **`execute-module-linked`** (- reading definition-sec-source-text-module-record-execute-module-1): The checked Assert reads it as: _module_.[[Status]] is one of ~linked~, ~evaluating~, ~evaluating-async~ or ~evaluated~, and _module_.[[Environment]] is not ~empty~. InnerModuleLinking sets ~linked~ only after InitializeEnvironment has set [[Environment]] and instantiated its declarations. *(Spec: sec-source-text-module-record-execute-module 1 (spec.html 28957))*
- **`initialize-environment-named-exports`** (- phrase ph-named-exports-resolvable): The checked Assert reads it as: for each ExportEntry Record _e_ of _module_.[[LocalExportEntries]] and [[IndirectExportEntries]], _module_.ResolveExport(_e_.[[ExportName]]) is a ResolvedBinding Record. The names star exports bring in are left out. *(Spec: sec-source-text-module-record-initialize-environment 2 (spec.html 28889))*
- **`lexical-goal-parse-position`** (- code Ecma.Grammar.lexicalGoalOf, - code Ecma.Grammar.Tree.goalAt, - code Ecma.Grammar.GoalsAt): Practical VM token-directed lexical goal selection. Element 0 of a |Script| or |Module| is scanned under `InputElementHashbangOrRegExp`, non-token trivia after that under `InputElementDiv`, and each real token under the lexical goal implied by the leaf or terminal matching it in the derivation (`Tree.goalAt`: `InputElementRegExp` for |RegularExpressionLiteral|, `InputElementTemplateTail` for |TemplateMiddle| and |TemplateTail|, `InputElementDiv` otherwise), evaluated at the post-`;` parse position after any semicolon §12.10 inserted (matching V8/SpiderMonkey/JSC on `let a\n/x/.test("x")` and `return\n/x/.test("x")`; §12's note "not affected by semicolon insertion" states only that `/` after an expression such as `a = b \n /hi/g` prevents ASI rather than re-reading a post-ASI token in the pre-ASI context). *(Spec: sec-ecmascript-language-lexical-grammar (spec.html 16545-16547))*
- **`asi-left-to-right`** (- code Ecma.Grammar.SynOpen, - code Ecma.Grammar.SynHit, - code Ecma.Grammar.NextASI, - code Ecma.Grammar.ValidASI, - code Ecma.Grammar.ASIOk): §12.10's "as the source text is parsed from left to right, a token (called the offending token) is encountered that is not allowed by any production of the grammar" is formalized directly by iterative left-to-right prefix reachability (`ValidASI`): when no derivation spans the input under the virtual semicolons inserted so far (`not SynDone`), `NextASI` takes the furthest boundary `f = 2 * p` reached from `(goal, ps, 0)` (`SynHit`), scans at `p` under `InputElementDiv`, and inserts a virtual semicolon at `p` at end of input or before an offending token preceded by a line terminator, `}`, or `)` (restricted to do-while's `;`). Rule 3 (`[no LineTerminator here]`) is subsumed because `Item.noLT` is part of `SynPrefix`/`SynDerives`. *(Spec: sec-rules-of-automatic-semicolon-insertion (spec.html 17230-17275))*
- **`cover-matched-tokens`** (- code Ecma.GrammarCtx.CoverIs, - code Ecma.Model.CoverLaws): §5.1.5's "The sequence of tokens originally matched by _p_ is parsed again using _n_ as the goal symbol" is formalized by `GrammarCtx.CoverIs`, which reparses the matched token sequence (preserving any virtual semicolons §12.10 inserted inside _p_ during the enclosing parse) without re-running `ASIOk` from scratch on _p_'s sliced text. *(Spec: sec-syntactic-grammar (spec.html 1502-1515))*

## 8. Data Sort Doubts & Ambiguities
From `decisions.md` (`Sort doubts` section):

#### `time-value-range`
- **Spec**: sec-time-values-and-time-range (spec.html 33764-33775); sec-epoch-nanoseconds (spec.html 34042-34048)
- **Doubt**: "time value" is defined without a range, the paragraph gives ±8.64 × 10^15; "epoch nanoseconds count" includes its range.
- **Decision**: The time value sort has no range; the epoch nanoseconds count sort keeps its range.

#### `undefined-object-terms`
- **Spec**: sec-ordinary-object-internal-methods-and-internal-slots (spec.html 12731-13296); sec-array-exotic-objects (spec.html 14310-14452); sec-built-in-function-objects (spec.html 14051-14177)
- **Doubt**: "extensible" has no dfn; exotic objects' "other essential internal methods use the definitions in 10.1"; "built-in" is about provenance, which state cannot decide.
- **Decision**: Tests by observation: [[Extensible]]; the method identity; an ordinary object whose [[Call]] is 10.3.1's.

#### `data-block-shared`
- **Spec**: sec-data-blocks (spec.html 4477-4563)
- **Doubt**: A Shared Data Block is called "a data block", yet headers say "a Data Block or a Shared Data Block".
- **Decision**: The two are disjoint (IsDataBlock, IsSharedDataBlock).

#### `binding-terms`
- **Spec**: sec-environment-records (spec.html 10224-11627)
- **Doubt**: "binding" has no dfn and no value; "strict", "mutable", "uninitialized" bindings neither.
- **Decision**: Residue; the env.emu readings give bindings their fields.

#### `undefined-instance-terms`
- **Spec**: sec-properties-of-regexp-instances (spec.html 40036-40048); sec-properties-of-array-iterator-instances (spec.html 41792-41843)
- **Doubt**: "an initialized RegExp instance" and the iterator "Instance" phrases are not defined terms.
- **Decision**: A RegExp instance whose [[RegExpMatcher]] is set; the iterator phrases read as "has the slots of".

#### `pattern-terms`
- **Spec**: sec-pattern-notation (spec.html 37797-37875); sec-runtime-semantics-unicodematchproperty-p (spec.html 39324-39353)
- **Doubt**: "single" has no dfn; "Unicode property name / value" are emu-not-ref and never defined.
- **Decision**: "single" is one character; property names and values come from the spec tables and the pinned UCD files.

#### `record-kind-terms`
- **Spec**: sec-private-names (spec.html 4706-4709); sec-synthetic-module-records (spec.html 28979-29175)
- **Doubt**: Private Name's [[Description]] is called an internal slot; Synthetic Module Record is a Module Record subclass only by implication.
- **Decision**: [[Description]] is a field; Synthetic Module Record has super Module Record.

#### `code-point-and-sign-terms`
- **Spec**: sec-source-text (spec.html 16311-16451); sec-mathematical-operations (spec.html 886-920)
- **Doubt**: "sequence of Unicode code points" is never defined; "non-negative" and "positive" have no definition.
- **Decision**: A List of code points (any "sequence of" values is a List of them in order; a CharSetElement that is not a List is a sequence of one character); ≥ 0 and > 0 on mathematical values, with +0 positive and -0 negative for Numbers.

#### `code-literal-code-points`
- **Spec**: sec-multiplicative-operators-runtime-semantics-evaluation 1 (spec.html 20422); sec-applystringornumericbinaryoperator 6.b (spec.html 21000-21024)
- **Doubt**: _opText_ is "the source text matched by |MultiplicativeOperator|", a sequence of code points, yet the parameter's type and step 6's `is` comparisons give it as a code literal (`/`, `%`); the spec never says what a code literal is as a value.
- **Decision**: A code literal is a String; `v is w` with w a String reads a List of code points v as the String of them (`isVals`, lean/Ecma/Ops/Leaf.lean), as a table's code cells are read (`codeKey`).

### Full Sort Doubt Inventory (from legacy `sorts-doubts.md`)

# Doubts: data sorts (sorts.emu)

Spec-issue candidates are marked **[spec issue]**.

## Records

- **Environment Record, PrivateEnvironment Record, Reference Record, Private Name, execution context, Realm Record, Script Record, WaiterList Record, ModuleRequest / LoadedModuleRequest / ImportAttribute Record** (their own clauses): the spec does not call these Records. It calls them a "specification type", "specification mechanism" or "specification device", or says one "consists of the following fields". They are Record kinds here because the spec makes them with "a new X" and reads their fields.
- **Private Name** (sec-private-names): [[Description]] is called an "internal slot", where every other specification type says "field". HasSlot cannot be used because the subject is often a String or Symbol. **[spec issue]**
- **Synthetic Module Record** (sec-synthetic-module-records): it is a subclass of Module Record only by implication ("In addition to the fields defined in Table Module Record Fields"). sec-abstract-module-records names only Cyclic Module Record and Source Text Module Record as subclasses. super="Module Record" is given. **[spec issue]** (editorial)
- **LoadedModuleRequest Record** (sec-modulerequest-record): it has ModuleRequest Record's fields plus [[Module]], but the spec does not make it a subtype and writes "a ModuleRequest Record or a LoadedModuleRequest Record" where both are allowed. The two are kept separate.
- **ResolvedBinding Record** (sec-abstract-module-records): it has no paragraph of its own. Its definition is the record-literal form in ResolveExport's row of the abstract-methods table.
- **ECMAScript code execution context** (sec-execution-contexts): it is a subtype of execution context only through "the additional state components". As a Record kind it is correct only if every such context comes from "a new ECMAScript code execution context" (lines 13871, 26804, 29257, 29503, 30492). The "a new execution context" sites (12166, 14456, 52023) are built-in, realm and host contexts, which is consistent.
- **Super Reference Record** (sec-reference-record-specification-type): it is defined by a field value ([[ThisValue]] is not ~empty~), not by a kind. The test is IsSuperReference, guarded by a Reference Record check because that is IsSuperReference's parameter type.
- **Memory event** (sec-memory-model-fundamentals): it includes "host-specific events", which have no definition. A host's event Records need a kind with super "Memory event". Otherwise they fail the test instead of stopping.
- **WriteSharedMemory / ReadModifyWriteSharedMemory** (sec-memory-model-fundamentals): the dfns are the bare names, and the Record literals use them, but the text also writes "X event".
  - ReadModifyWriteSharedMemory event (190) and its plural (191) must fold to the record sort ReadModifyWriteSharedMemory at data time.
  - WriteSharedMemory event (189) is an overlay test that delegates to WriteSharedMemory (35).
  - The literal "WriteSharedMemory { … }" must create kind 35.
- **implementation-defined Completion Record** (sec-debugger-statement-runtime-semantics-evaluation): its one use is the construction "Return a new implementation-defined Completion Record." That phrase needs its own meaning, a host choice. As a test the sort accepts any Completion Record.
- **fully / populated** (sec-property-descriptor-specification-type): the dfn is the compound "fully populated Property Descriptor", and the inventory splits it in two. "fully" carries the guarded definition and "populated" is *true*. Folding the compound into one adjective at data time would be cleaner.
- **possibly empty** (sec-list-and-record-specification-type): the inventory splits "possibly" (109) from "empty" (110), but "a possibly empty List" is a List of any length.
  - The entry is named "possibly empty". The data pass must fold the pair and drop the "empty | List" pairing for its use (line 20093, "_restSub_ is a possibly empty List"). Otherwise IsEmpty wrongly applies.

## Objects

- **extensible** (sec-ordinary-object-internal-methods-and-internal-slots): "extensible" has no dfn. Only the em-term "non-extensible" exists, and it is defined by observation (sec-invariants-of-the-essential-internal-methods).
  - The test reads [[Extensible]]. For an object without that slot (a Proxy, for example) the test reaches a prose step, which is residue.
  - All 5 uses are about ordinary objects or functions the spec creates.
  - **[spec issue]**: define "extensible", for example as [[Extensible]] for ordinary objects.
- **Array / String / arguments exotic object, TypedArray, module namespace exotic object** (sec-array-exotic-objects, sec-string-exotic-objects, sec-arguments-exotic-objects, sec-typedarray-exotic-objects, sec-module-namespace-exotic-objects): their dfns say "its other essential internal methods use the definitions in 10.1". That is read to cover Table 5's [[Call]]/[[Construct]], which 10.1 does not define, so the tests reject an object that has either method (HasMethod). It is unclear whether Table 5 counts as "other essential internal methods". **[spec issue]** (wording)
- **ordinary, ECMAScript function object, built-in, bound function / Proxy / exotic objects, immutable** (sec-object-internal-methods-and-internal-slots): the steps "is not the internal method defined in <clause>" use a new phrase in sorts.emu that maps to IsOrdinaryMethod (prim 22). Its meaning already compares the method's clause with any clause, but its doc in object.emu still says "ordinary object internal method" and should be generalized.
- **Proxy exotic object** (sec-proxy-object-internal-methods-and-internal-slots): the dfn works by internal methods, not by [[ProxyHandler]], and the test follows the dfn. The two agree in every reachable state, because only ProxyCreate installs those methods, and it also sets [[ProxyHandler]] and [[ProxyTarget]].
- **ECMAScript function object** (sec-ecmascript-function-objects): it has no dfn. The test is an ordinary object whose [[Call]] is the one in 10.2.1. Having [[ECMAScriptCode]] would be an equivalent reading.
- **built-in** (sec-built-in-function-objects): "built-in object" (4.4) is about where an object comes from, which state cannot decide. The adjective occurs only in "built-in function object", so the test is an ordinary object whose [[Call]] is the one in 10.3.1. That would be wrong if the adjective were ever used on a non-function.
- **immutable / prototype exotic object** (sec-immutable-prototype-exotic-objects): the inventory splits the single dfn immutable-prototype-exotic-object, and "prototype exotic object" is not a term on its own. Both entries carry the whole test. Folding them at data time would be cleaner.
- **initialized RegExp instance** (sec-properties-of-regexp-instances): RegExpBuiltinExec's parameter type is not defined anywhere. It is read as a RegExp instance whose [[RegExpMatcher]] is no longer *undefined*. Callers guarantee only RequireInternalSlot(R, [[RegExpMatcher]]). **[spec issue]** (undefined term)
- **iterator object** (sec-iterator-interface): conforming to the iterator interface is a requirement on how `next` behaves, not a property of state, so the sort is residue. Its one use is EnumerateObjectProperties' return type, which is implementation-defined.
- **Array Iterator Instance, RegExp String Iterator Object Instance, For-In Iterator instance** (sec-properties-of-array-iterator-instances, sec-properties-of-regexp-string-iterator-instances, sec-properties-of-for-in-iterator-instances): these are not defined terms. They occur only in "has all of the internal slots of a X", so each test is that clause's slot table. Capitalization and wording vary. **[spec issue]** (editorial)
- **Generator** (sec-properties-of-generator-instances): testing by [[GeneratorState]] also admits the objects CreateIteratorFromClosure makes (non-empty [[GeneratorBrand]]). That matches the spec's own return types ("a Generator" from CreateMapIterator and IteratorZip).
- **ArrayBuffer / SharedArrayBuffer** (sec-properties-of-the-arraybuffer-instances, sec-properties-of-the-sharedarraybuffer-instances): the slot tables do not separate the two. The tests inline IsSharedArrayBuffer's step ([[ArrayBufferData]] is a Shared Data Block). Calling IsSharedArrayBuffer would recurse once headers are checked, because its parameter type is these two sorts. [[ArrayBufferDetachKey]] would be an equivalent test for ArrayBuffer.
- **Uint8Array** (sec-validateuint8array): it has no dfn. The test is the Boolean form of ValidateUint8Array: [[TypedArrayName]] is *"Uint8Array"*.
- **Promise** (sec-properties-of-promise-instances): alg=IsPromise, whose parameter is "an ECMAScript language value". Once parameter headers are checked, testing a Record would stop instead of returning *false*. A guard would fix it: "If _v_ is not an ECMAScript language value, return *false*."
- **data property / accessor property** (sec-object-type): both dfns are prose. PropertyIsKind reads the kind given at OwnPropertyCreate and OwnPropertyReplace. The subject is an own property, as OwnPropertyLookup returns it.
- **(no entry)**: async iterator object, IteratorResult object, host-defined exotic object, callable, and "built-in function object" as a noun are not in the inventory.

## Values

- **code point / Unicode code point** (sec-source-text): ECMA-262 has no dfn; the term comes from the Unicode Standard. The test uses the U+0000–U+10FFFF range that sec-source-text states.
- **code unit** (sec-ecmascript-language-types-string-type): String elements are "16-bit unsigned integer values" treated as UTF-16 code units, yet the text writes "the numeric value of a code unit". The model identifies code units and code points with their numeric values, so code unit, code point, byte value and integer overlap.
- **surrogate** (sec-ecmascript-language-types-string-type): only "leading surrogate" and "trailing surrogate" are defined. The bare noun is tested as their union, [0xD800, 0xDFFF]. "leading" and "trailing" each carry their compound's full definition, including "is a code unit".
- **character** (sec-pattern-semantics): defined relative to its pattern (BMP: a code unit; Unicode: a code point). The sort's context phrase ph-character-of-pattern reads the pattern's mode from the _regexpRecord_ the steps or header name. A header or test that names none (CharacterRange, CharSetElement's test) leaves the pattern open, and the test there is the union, a code point.
- **CharSetElement** (sec-pattern-notation): defined relative to _regexpRecord_.[[UnicodeSets]], which its test does not receive, so the test is the union of the cases.
- **CharSet** (sec-pattern-notation): a mathematical set, held as a List. The test rejects duplicates and counts a one-character sequence as equal to its character.
- **single** (sec-pattern-notation): it has no dfn. Its one use is "Assert: _charSet_ contains only single code points", read as "one character".
  - Under the conjunctive meaning, a one-element List passes "single" but fails "code point", although the clause makes a character and a sequence of one character interchangeable.
  - **[spec issue]**: use the wording "consists of a single character".
- **empty** (sec-list-and-record-specification-type): its one standalone use is "an empty CharSet". IsEmpty covers CharSets only through their List representation. "Return the empty CharSet" (line 38959) is a construction, not a test.
- **time value** (sec-time-values-and-time-range): the dfn sentence (a finite integral Number, or *NaN*) gives no range, but the paragraph gives ±8.64 × 10^15. LocalTime's note says its input "may be any Number value".
  - The test follows the dfn sentence. If the range were part of the definition, "_tv_: a finite time value" checks near the boundary would fail.
  - **[spec issue]** (ambiguity)
- **epoch nanoseconds count** (sec-epoch-nanoseconds): the dfn includes the range MinEpochNanoseconds..MaxEpochNanoseconds, and the test keeps it.
  - GetUTCEpochNanoseconds and GetNamedTimeZoneEpochNanoseconds are reached from UTC(_t_) with _t_ deliberately not limited to the time value range. Their results can exceed the bound by up to a day, and return-type checks would then fail. **[spec issue]**
  - MinEpochNanoseconds and MaxEpochNanoseconds must resolve as emu-eqn constants. TimeConst covers only HoursPerDay … msPerDay.
- **non-negative / positive** (sec-mathematical-operations): neither has a definition in ECMA-262. sec-ecmascript-language-types-number-type counts +0𝔽 as positive and -0𝔽 as negative.
  - "non-negative" Number is tested as [+0𝔽, +∞𝔽], which excludes -0𝔽 and *NaN*.
  - "positive" is used only with integers, so only its mathematical sense (> 0) is given.
- **odd** (sec-mathematical-operations): not defined; only "odd significand" is. "an odd integral Number" is read as ℝ(_v_) being odd.
- **byte / byte value** (sec-data-blocks): "byte" has no dfn. Its one use, "For each byte _byte_ of _toEncode_", is over a List of byte values, so it delegates to "byte value". It is better folded as a variant at data time. The inventory has only the plural "byte values" (167), so the entry is the singular dfn under that id.
- **integer index / array index** (sec-object-type): CanonicalNumericIndexString is used inside an overlay body, not as alg=, because it returns a Number or *undefined*. The lower bound +0𝔽 excludes -0𝔽, so InInterval's Number case must honour -0𝔽 < +0𝔽.
- **sequence of Unicode code points** (sec-source-text): "sequence" is never defined. The List reading is the spec's own: ParseText uses StringToCodePoints' "List of code points", and UnicodeMatchProperty returns "the List of Unicode code points _p_". **[spec issue]**: say "List of code points" throughout.
- **Plurals of Known sorts** (46 ECMAScript language values, 51 property keys, 60 Strings, 152 integers) must fold to Known 14, 15, 2 and 9 at data time.

## Other

- **error** (sec-parsetext): `spec.html` never defines the sort `error` (#3868), while ten caller steps test `is a List of errors`. SpecTec defines `@sort-error` (`Helpers.spectec`) as an `Object` with an `[[ErrorData]]` internal slot (notated under `ParseTextErrorObjects`, write-up 05).
- **binding, strict, mutable, uninitialized** (sec-environment-records): `spec.html` manipulates bindings without defining a `Binding Record` sort. SpecTec (`00-decls.spectec`, `Helpers.spectec`, `S09.spectec`) models bindings as `Record`s with `[[Value]]`, `[[Mutable]]`, `[[Strict]]`, `[[Initialized]]`, `[[Deletable]]`, `[[Module]]`, and `[[BindingName]]` fields and defines `@sort-binding`, `@sort-strict` (*false* on indirect bindings), `@sort-mutable`, and `@sort-uninitialized`.
- **internal slot name** (sec-object-internal-methods-and-internal-slots): the spec lists no closed set of slot names. Slot names, internal-method names and Record field names share the [[F]] notation and one name space in the model (FieldId), so IsInternalSlotName accepts any [[F]] name.
- **grammar symbol / nonterminal** (sec-context-free-grammars): Val has a nonterminal form (.nt) but no terminal-symbol form. Contains is called with terminals (Contains `await`, Contains `super`; lines 25301, 26660, 26962), so IsGrammarSymbol under-approximates until terminals become values and a phrase "the terminal `x`" exists.
- **nonterminal** (sec-context-free-grammars): 3 of its 5 uses are "If _child_ is an instance of a nonterminal". There the sort is InstanceOf's operand, not a test of a symbol value, and that phrase needs its own meaning.
- **Unicode property name / Unicode property value** (sec-runtime-semantics-unicodematchproperty-p, sec-runtime-semantics-unicodematchpropertyvalue-p-v): both are marked emu-not-ref and never defined. Membership comes from spec tables or from the versioned, external UCD files PropertyAliases.txt and PropertyValueAliases.txt, so both are residue.
  - The runtime uses at lines 39082 and 39334 are compound phrases that need their own meanings.
  - UnicodeMatchPropertyValue's return type does not say which property the value belongs to.
  - **[spec issue]**
- **Data Block / Shared Data Block** (sec-data-blocks): the clause calls a Shared Data Block "a data block", yet headers say "a Data Block or a Shared Data Block" and the text says the two "can be distinguished". They are read as disjoint (IsDataBlock, IsSharedDataBlock). **[spec issue]**: is a Shared Data Block a Data Block?
- **Matcher, MatcherContinuation, Job Abstract Closure, read-modify-write modification function** (sec-pattern-notation, sec-jobs, sec-arraybuffer-notation): each is defined by its signature, and read-modify-write also by purity and atomicity, none of which can be checked on a value.
  - ClosureKind reads the closure literal's kind instead. Every instance in the spec comes from "a new S with parameters …", and host Jobs are assumed to be such literals too.
  - "Job Abstract Closure" has no dfn of its own; the dfn is "Job".
- **Slot and method tests generally**: HasSlot and HasMethod take (slot, subject) and stop with sortError on a non-Object. Every slot or method test is therefore steps that begin "If _v_ is not an Object, return *false*."

## 9. SpecTec Translation & AST Simplifications
- **Elimination of `.emu` overlay channels**: Removed `<emu-phrase>`, `<emu-reading>`, `<emu-rule-reading>`, `<emu-step-patch>`, `<emu-erratum>`, `<emu-permanent>`, `spec/formal/*.emu`, `Decls.phrases`, `Expr.prose`, `Ins.readings`, `Expr.mutate`, `Expr.readings`, `LitForm`, `AltForm`, `ConnForm`, `Article`, `Xref`, and SHA-256 text hashes.
- **Materialization of specialized helper algorithms (`Plan.decl`)**: Helper algorithms generated previously in memory by `Spec.Plan.ofSrc` (`d.algs`) and prose phrases (`Phrases_*.lean`) are materialized as explicit SpecTec `def` declarations in `spec/spectec/clauses/Helpers.spectec` with persistent IDs in `spec/ids/clause-ids.txt`.
- **Structured `SortTest` replacing `PhraseMeaning`**: `SortDef` drops `context` (English phrase template) and replaces `PhraseMeaning` on `SortDef.test` with a clean algebraic `SortTest` (`none | alg | prim`) reflecting runtime sort membership tests directly.
- **No `Spec.Plan` / `Such` / `Macro` lowering in `Ecma/Lower/`**: SDO row binding adjustments, `choice` date lowering (`TimeFromYear`), `calls`, and table rewrites are either materialized directly in `.spectec` sources or simplified into clean linear lowering passes without prose/macro expansion.
- **Builtin error creation**: `Engine.Host.Core` calls `Known.algNewError` (referencing the `NewError` SpecTec algorithm directly) instead of `Known.phNewError`.
- **Known Errata-Switching Tests**: JS run tests specifically exercising runtime toggling away from the active reading are annotated with `// needs: errata-switching` and skipped unless run in an errata-switching harness.

- **Stale HTML SDO rows (`prods []`)**: Unreachable rows in `spec.html` naming removed grammar productions (such as §12.9.3.2 MV's `` DecimalIntegerLiteral :: `0` `` row left behind by PR #3988) are preserved with `prods []` in SpecTec solely for byte-exact `spec.html` round-tripping (`scripts/html_bijection.py`).
