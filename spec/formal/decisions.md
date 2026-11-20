# Spec decisions: the register of ambiguities and defects of the pinned ECMA-262 text

spec.html is tc39/ecma262 at b1eaed82f (external/ecma262); every `spec.html N` is a line of it.

One row per decision the formalization takes because the pinned spec.html is ambiguous, defective or leaves a choice
open: an erratum (errata.txt), an overlay reading or phrase meaning that interprets the text, a model choice, a
host-choice default of the test hosts (FastHost's and RefHost's choices), a sort doubt
(sorts-doubts.md). `python3 scripts/spec_decisions.py --spec <spec.html>` (//:spec_decisions_test) checks it; a
failure listed in decisions-gaps.txt is not reported, and that file only shrinks.

Row format: `## <id>`, then the fields, each a `- key:` line (continuation lines indented two spaces):
- `spec`: `<clause id> [step] (spec.html N[-M])`, `;`-separated; each line lies inside its clause.
- `quote`: the text's own words, verbatim and markup-stripped; `…` separates fragments. Each occurs in the cited
  lines.
- `text`: the ambiguity or defect; `decision`: what the model does; `scope`: where it applies.
- `decided`: user or coordinator, the date, the source (bus #, merge, brief).
- `covers`: at least one sub-bullet `  - <kind> <name>`: erratum, reading (overlay reading id), overlay (element id,
  a phrase's among them), silent (a default the test hosts take, by the name of its definition), doubt (sorts-doubts.md bold lead), file (under
  spec/ or docs/), host (a choice primitive FastHost or RefHost answers, by its Known name without the `p`), code (a
  Lean declaration under lean/ by its full name: def, structure, inductive, constructor or field).
- `pending` (optional): sub-bullets `  - <task>: <kind> <name>`, a reference that task adds; the check fails once it exists.
- `note` (optional): evidence (tests, executor facts), not part of the claim.
- `report`: docs/spec-issues paths and SHORTLIST items, upstream issues, or `-`. A row covering an erratum names
  its write-up, and each write-up's header has a `- **Model erratum:**` line naming errata of errata.txt.

Classes:
- **Erratum** (the user's): the text is defective where a run reaches it. The defect is one of these:
  - its literal result contradicts another normative statement;
  - an Assert or `!` can fail in a conforming execution;
  - a value has the wrong kind, or a name is unbound;
  - a case, row or step is missing, so a reachable step has no meaning;
  - the step is vague, and test262 or every engine shows one intended result that some literal reading misses.

  The model runs or stops the literal text, carries the fix as `proposed` (and `test262` where that differs), and
  has a write-up.
- **Proposed normative change** (the user's): the text is definite and every implementation departs from it in
  the same way; the model carries the change as a switchable reading (resolution `proposed`, kind `proposal` in
  errata.txt), listed for the committee apart from the defects.
- **Interpreting reading** (the coordinator's): the text uses a term or notation it does not define. Every plausible
  reading gives the same results, or one reading is presupposed by the rest of the text. The overlay supplies that
  reading. The row has no write-up; an editorial line in SHORTLIST 19 is enough.
- **Model choice** (the coordinator's, or the user's where the row says so): the text is definite, or it leaves the
  latitude open. The decision is the model's representation, its scope or a narrowing it accepts. It has a row and
  never a write-up. Host-choice defaults are the test hosts' answers to open choices; they keep their section.
- **Restating**: the overlay gives the text's own results, by notation, synonyms or articles, a condition split, a
  cited definition, an Assert of what the text presupposes, or a choice the text leaves open, passed to a host
  primitive whose law is the text's constraint. The entry is a line of readings-restating.txt with its reason, and
  has no row.

Every choice primitive of the test hosts has a row for its default (`host` covers). Policy for errata:
docs/arc/esl-semantics.md §3.8.

# Errata

Fixed upstream, no longer rows (their errata retired at b1eaed82f; the write-ups stay, marked so):
TypedArrayWithSetElementAbrupt and TypedArrayFilterKeptUndefined (4feb0272b, PR #3979;
docs/spec-issues/07-typedarray-with-filter-bang.md), IsLooselyEqualBooleanAbrupt (8a3e4aae, PR #4067;
docs/spec-issues/08-islooselyequal-boolean-bang.md), RevalidateAtomicAccess (5e0f8b33, PR #3926;
docs/spec-issues/34-revalidate-atomic-access.md), ReadsBytesFromUnboundResult (d8cb8772, PR #4064;
docs/spec-issues/22-reads-bytes-from-unbound-result.md).

## number-multiply-zero-sign
- spec: sec-numeric-types-number-multiply (spec.html 1802); sec-numeric-types-number-multiply 6 (spec.html 1820)
- quote: Return 𝔽(ℝ(_x_) × ℝ(_y_)).
- text: Step 6, "Return 𝔽(ℝ(_x_) × ℝ(_y_)).", gives +0𝔽 for `+0 × -5`, because 𝔽(0) is +0𝔽. The clause's description is
  "according to the rules of IEEE 754-2019 binary double-precision arithmetic", which give -0𝔽. Steps 4-5 handle only
  -0𝔽 operands.
- decision: Pending. The literal step runs. The proposed reading returns -0𝔽 for +0𝔽 times a negative finite Number, in
  either order.
- scope: Number::multiply with a +0 operand and a negative finite one.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum NumberMultiplyZeroSign
- report: docs/spec-issues/01-number-multiply-zero-sign.md, SHORTLIST 8

## gather-available-ancestors-empty-cycle-root
- spec: sec-gather-available-ancestors 1.a (spec.html 27650)
- quote: If _execList_ does not contain _ancestorModule_ and _ancestorModule_.[[CycleRoot]].[[EvaluationError]] is
  ~empty~, then
- text: Step 1.a reads a field of [[CycleRoot]], which may be ~empty~.
- decision: Literal: a run that reaches the step with an ~empty~ cycle root stops there; the proposed reading asserts
  the cycle root and tests its error.
- scope: async module graphs (GatherAvailableAncestors).
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum GatherAvailableAncestorsEmptyCycleRoot
- report: docs/spec-issues/02-gather-available-ancestors-empty-cycle-root.md (upstream: issue #3766 and PR #3769, open on 2026-11-19)

## builtin-return-completion
- spec: sec-builtincallorconstruct 10.b.iii (spec.html 14125)
- quote: Return Completion(_result_).
- text: The step returns a built-in's normal result as is, so an async built-in's promise (AsyncBlockStart) fulfils
  with undefined: every `Array.fromAsync` call.
- decision: test262: a normal result is returned as a return completion.
- scope: built-in async functions.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum BuiltinReturnCompletion
- report: docs/spec-issues/03-builtin-async-return-value.md, SHORTLIST 1

## execute-module-async-dispose
- spec: sec-source-text-module-record-execute-module 4.b (spec.html 28972)
- quote: Perform AsyncBlockStart(_capability_, _module_.[[ECMAScriptCode]], _moduleContext_).
- text: A module with top-level await never disposes its top-level `using`/`await using` resources: the step lacks
  the DisposeResources call the synchronous branch has.
- decision: test262: the async branch disposes them as the synchronous one does.
- scope: modules with top-level await.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum ExecuteModuleAsyncDisposeResources
- report: docs/spec-issues/04-execute-module-tla-dispose.md, SHORTLIST 5

## parsetext-error-objects
- spec: sec-parsetext 4 (spec.html 16442); sec-parsetext (spec.html 16428-16450); sec-parsepattern 1.a (spec.html
  39497); sec-parsepattern-annexb 1.a (spec.html 54121)
- quote: Return a List of one or more *SyntaxError* objects representing the parsing errors and/or early errors. … Let
  _parseResult_ be a List containing one or more *SyntaxError* objects.
- text: ParseText 4, "Return a List of one or more *SyntaxError* objects representing the parsing errors and/or early
  errors", and ParsePattern 1.a create objects inside a static semantics, and name no realm. Callers observe only
  whether the List is empty.
- decision: Literal, with no stop: no step reads an object from the List. The List is the machine's own: the early
  errors of the innermost nodes that have any, in source order, and one error for a failed goal; only its non-emptiness
  is the text's (R22). The proposed reading returns errors, which callers turn into *SyntaxError* objects of their
  realm.
- scope: parse failures: ParseText, ParsePattern and their callers.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum ParseTextErrorObjects
  - overlay ph-syntax-errors
  - doubt error
- report: docs/spec-issues/05-parsetext-error-objects.md (related: issues #3868 and #1462, open; neither reports it)

## dowait-sync-timeout
- spec: sec-dowait 28.a-30 (spec.html 47159-47163)
- quote: Perform SuspendThisAgent(_waiterList_, _waiterRecord_). … If _mode_ is ~sync~, return
  _waiterRecord_.[[Result]].
- text: A timed-out synchronous `Atomics.wait` returns "ok" and leaves its waiter in the list, so a second wait fails
  AddWaiter's Assert.
- decision: test262: a timed-out wait removes its waiter and returns "timed-out".
- scope: Atomics.wait with a finite timeout.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum DoWaitSyncTimeout
- report: docs/spec-issues/06-dowait-sync-timeout.md, SHORTLIST 2

## atomics-waitasync-timeout-assert
- spec: sec-enqueueatomicswaitasynctimeoutjob 1.b.ii (spec.html 47187)
- quote: Assert: ℝ(_timeOfJobExecution_) ≥ _waiterRecord_.[[TimeoutTime]] (ignoring potential non-monotonicity of time
  values).
- text: The Assert can fail in a conforming implementation: its truth depends on implementation-defined timing
  choices. A host whose clock has millisecond resolution may run the Job of a sub-millisecond wait before its clock
  ticks, at a time value below a fractional [[TimeoutTime]]. A run that fails it on a host that takes the Job before
  its delay (against §9.5.6's "after at least") shows that host's defect, not this one.
- decision: Literal; a run stops at 1.b.ii when the Assert fails. The parenthesis on non-monotonicity is
  commentary (phrase ph-time-at-least): a clock that runs backward fails the comparison as any other reading would,
  and the run stops with this erratum, since excusing it would need the clock's history, which the state does not
  give. The proposed reading, write-up 09's second fix, states the Assert for the integral time: "_timeOfJobExecution_
  ≥ 𝔽(_waiterRecord_.[[TimeoutTime]]) rounded down to an integral Number"; it should hold in every conforming run,
  so for the same reason it is unchecked (permanent.emu, assert-provenance) rather than a stop.
- scope: Atomics.waitAsync with a timeout.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2); stop at 1.b.ii: coordinator
  2026-10-19 (#12376)
- covers:
  - erratum AtomicsWaitAsyncTimeoutAssert
- report: docs/spec-issues/09-atomics-waitasync-timeout-assert.md, SHORTLIST 13

## atomics-waitasync-negative-delay
- spec: sec-enqueueatomicswaitasynctimeoutjob 4 (spec.html 47195)
- quote: Perform HostEnqueueTimeoutJob(_timeoutJob_, _currentRealm_, 𝔽(_waiterRecord_.[[TimeoutTime]]) - _now_).
- text: The step can pass a negative delay to HostEnqueueTimeoutJob, which takes "a non-negative finite Number".
- decision: Literal: a run stops at the step when the delay is negative.
- scope: Atomics.waitAsync with a timeout.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum AtomicsWaitAsyncTimeoutNegativeDelay
- report: docs/spec-issues/09-atomics-waitasync-timeout-assert.md, SHORTLIST 13

## utc-epoch-nanoseconds-nan
- spec: sec-utc-t 1 (spec.html 34294); sec-getutcepochnanoseconds 4 (spec.html 34072)
- quote: If _t_ is not finite, return *NaN*. … Assert: _epochMilliseconds_ is an integral Number.
- text: UTC(_t_) for a local time far past the time value range reaches GetUTCEpochNanoseconds' failing Assert
  (`new Date(0).setHours(1e21)`).
- decision: Literal: a run stops at GetUTCEpochNanoseconds 4; the proposed reading returns NaN first.
- scope: Date setters and UTC with out-of-range local times.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum GetUTCEpochNanosecondsNaN
- report: docs/spec-issues/10-utc-large-local-time.md, SHORTLIST 16 (upstream: PR #3464, open, adds the range check)

## getmatchstring-start-after-end
- spec: sec-regexpbuiltinexec 13.b (spec.html 39825); sec-getmatchstring 1 (spec.html 39976)
- quote: Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of
  _string_. … Assert: _match_.[[StartIndex]] ≤ _match_.[[EndIndex]] ≤ the length of _string_.
- text: `/u` with lastIndex inside a surrogate pair reports a match one code unit late and, for an empty match, a
  Match Record that ends before it starts, failing GetMatchString's Assert; engines disagree.
- decision: Literal: a run stops at GetMatchString 1 under RegExpBuiltinExec.
- scope: Unicode-mode RegExps with lastIndex inside a surrogate pair or at the end.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum GetMatchStringStartAfterEnd
- report: docs/spec-issues/11-regexp-lastindex-inside-surrogate-pair.md, SHORTLIST 10

## async-block-start-await-result
- spec: sec-asyncblockstart 4 (spec.html 52421)
- quote: Assert: _result_ is ~unused~.
- text: The Assert that _result_ is ~unused~ fails when the closure is an await in an async module or function body
  that returns ~empty~.
- decision: test262: the Assert admits ~unused~ or ~empty~.
- scope: AsyncBlockStart.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum AsyncBlockStartAwaitResult
- report: docs/spec-issues/12-asyncblockstart-await-result.md (upstream: issue #3435, open; PR #4018 closed unmerged)

## promise-job-abrupt-completion
- spec: sec-newpromisereactionjob 1.h-1.i (spec.html 50688-50690); sec-jobs (spec.html 12140-12328)
- quote: If _handlerResult_ is an abrupt completion, then … The Abstract Closure must return a normal completion,
  implementing its own handling of errors.
- text: §9.5 requires a Job's Abstract Closure to return a normal completion, but NewPromiseReactionJob returns the
  throw completion of a resolving function.
- decision: Literal: a run stops at sec-jobs under NewPromiseReactionJob when it does.
- scope: promise jobs whose derived resolving functions throw.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum PromiseJobAbruptCompletion
- report: docs/spec-issues/13-promise-job-abrupt-completion.md

## native-function-initial-name
- spec: sec-function.prototype.tostring 3 (spec.html 31669)
- quote: The representation must have the syntax of a |NativeFunction|. Additionally, if _func_ has an [[InitialName]]
  internal slot and _func_.[[InitialName]] is a String, the portion of
- text: The step asks for a NativeFunction-syntax String whose PropertyName portion is [[InitialName]]; for some
  names no String meets both.
- decision: Literal: NativeFunctionSource's law carries both requirements; the default host answers where a String meets
  both; where none does (a non-empty [[InitialName]] no NativeFunctionAccessor? PropertyName matches), the host has no
  answer to give and the step is residue (not an erratum stop).
- scope: Function.prototype.toString of built-ins.
- decided: coordinator 2026-10-17 (bus #5154); user 2026-10-18 (U2)
- covers:
  - erratum NativeFunctionInitialName
- report: docs/spec-issues/14-nativefunction-initialname.md (related: PR #2695, open)

## synthetic-module-link-resets
- spec: sec-smr-Link 1 (spec.html 29138)
- quote: Let _realm_ be _module_.[[Realm]].
- text: Link of a Synthetic Module Record creates a new environment on every call, resetting bindings set by
  SetSyntheticModuleExport.
- decision: Literal, with no stop; the proposed reading returns when [[Environment]] exists.
- scope: Synthetic Module Records linked twice (host-created).
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
- covers:
  - erratum SyntheticModuleLinkResets
- report: docs/spec-issues/15-synthetic-module-link.md (upstream: issue #3989, open)

## createdynamicfunction-private-identifiers
- spec: sec-createdynamicfunction 24 (spec.html 31527)
- quote: If _expr_ is a List of errors, throw a *SyntaxError* exception.
- text: CreateDynamicFunction does not check AllPrivateIdentifiersValid: `new Function("o", "return o.#f")` reaches
  MakePrivateReference's failing Assert.
- decision: proposed: the body's and the parameters' private identifiers are checked, a SyntaxError otherwise (the
  test262 reading checks the body only, which is all test262 asserts).
- scope: Function, GeneratorFunction, AsyncFunction constructors.
- decided: coordinator 2026-10-13 (merge deb676137 esl-read); user 2026-10-18 (U2); user 2026-11-19 (the proposed
  reading is the default)
- covers:
  - erratum CreateDynamicFunctionPrivateIdentifiers
- report: docs/spec-issues/20-dynamic-function-private-identifiers.md, SHORTLIST 3

## identity-escape-join-controls
- spec: sec-patterns (spec.html 37018); sec-regular-expressions-patterns (spec.html 53870)
- quote: [~UnicodeMode] SourceCharacter but not UnicodeIDContinue
- text: Under Unicode 15.1 and later, ZWNJ and ZWJ are UnicodeIDContinue. So `/\<ZWNJ>/` without `u` is a SyntaxError, a
  normative change that no edition records.
- decision: test262 and proposed (`kind="proposal"`): IdentityEscape admits ZWNJ and ZWJ again (`reading="test262 proposed"`).
  An Annex B overlay in effect applies to the definition the reading gives as to the pinned one (GL.alts), so on an
  Annex B host B.1.2's IdentityEscape stands in place of the reading. Both `test262` and `proposed` run with
  `rulesUnder` checking `sel · != .literal`.
- scope: non-Unicode-mode patterns. On an Annex B host, B.1.2's IdentityEscape stands in place of the reading.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); the Annex B case coordinator 2026-10-18 (review of
  esl-annexb-meaning-regexp); user 2026-10-18 (U2); Step 4C update 2026-11-20 (`kind="proposal"`, `reading="test262 proposed"`)
- covers:
  - erratum IdentityEscapeJoinControls
- report: docs/spec-issues/21-identityescape-zwnj-zwj.md, SHORTLIST 11

## lone-property-general-category
- spec: sec-compiletocharset 2 (spec.html 38775)
- quote: If UnicodeMatchPropertyValue(`General_Category`, _s_) is a Unicode property value or property value alias for
  the General_Category (gc) property listed in PropertyValueAliases.txt, then
- text: Step 2 calls UnicodeMatchPropertyValue(General_Category, _s_) before testing that _s_ is a
  General_Category value, failing its Assert for a lone binary property name.
- decision: test262: the test comes first.
- scope: `\p{X}` with a lone name.
- decided: coordinator 2026-10-13 (merge deb676137 esl-read); user 2026-10-18 (U2)
- covers:
  - erratum LonePropertyGeneralCategoryAssert
- report: docs/spec-issues/24-lone-property-gc-assert.md, SHORTLIST 6 (upstream: issue #3586 and PR #3587, open)

## split-code-unit-strings
- spec: sec-string.prototype.split 10.d (spec.html 36562)
- quote: Let _codeUnits_ be a List consisting of the sequence of code units that are the elements of _head_.
- text: With an empty separator, step 10.d's List of code units goes to CreateArrayFromList, whose argument is a List
  of ECMAScript language values; a code unit is not one.
- decision: test262: the List holds the substrings of _head_ of one code unit each, in order.
- scope: String.prototype.split with an empty separator.
- decided: user 2026-10-16 (briefs/fixup/esl-split-codeunits.md: 'Erratum, test262 behaviour'; the errata approval)
- covers:
  - erratum SplitCodeUnitStrings
- report: docs/spec-issues/37-split-code-units.md, SHORTLIST 19

## init-happens-before-overlap
- spec: sec-happens-before (spec.html 53121); sec-memory-model-fundamentals (spec.html 52829)
- quote: _eventA_.[[Order]] is ~init~, and _eventA_ and _eventB_ have overlapping memory ranges. … the ranges are not
  equal
- text: Happens-before orders an ~init~ write only before events with overlapping memory ranges, and "overlapping"
  excludes equal ranges; the ~init~ writes are 1 byte each, so a 1-byte event at the same byte has an equal range and
  is not ordered after the ~init~ write.
- decision: Literal, with no stop: the memory-model meaning keeps the text's "overlapping" (HB.init); the proposed
  reading is "do not have disjoint memory ranges" with the event itself excluded.
- scope: the memory model (multi-agent); 1-byte accesses in an agent with no happens-before chain from the block's
  creator.
- decided: user 2026-10-18 (#11401: record spec issue 48 like the other errata)
- covers:
  - erratum InitHappensBeforeOverlap
- report: docs/spec-issues/48-init-overlap-equal-ranges.md

## memory-range-same-block
- spec: sec-memory-model-fundamentals (spec.html 52829); sec-reads-bytes-from (spec.html 53046); sec-coherent-reads
  1.c.ii (spec.html 53164)
- quote: Let the memory range of a Shared Data Block event _e_ be the Set of all integers in the interval from
  _e_.[[ByteIndex]] (inclusive) … has _readEvent_.[[ByteIndex]] + _i_ in its memory range … that has _byteLocation_ in
  its memory range
- text: A memory range is a Set of integers with no [[Block]], so reads-bytes-from lets a read take a byte from a
  write to another Shared Data Block at the same index, and coherent reads 1.c.ii rejects an execution for such a
  write between the write read from and the read; with two blocks in one agent a read can return the other block's
  byte.
- decision: Proposed reading (resolution `proposed`, no stop): both tests also ask that the write's [[Block]] is the
  read's. The memory model's meaning (Ecma.MemoryModel.Rbf.Valid, Ecma.MemoryModel.CoherentReads) reads it.
- scope: the memory model; every read of a Shared Data Block (the single-agent value and law L2 rest on it).
- decided: user 2026-10-21 (#17617)
- covers:
  - erratum MemoryRangeSameBlock
  - code Ecma.MemoryModel.Rbf.Valid
  - code Ecma.MemoryModel.CoherentReads
  - file docs/spec-issues/50-memory-range-same-block.md
- report: docs/spec-issues/50-memory-range-same-block.md, SHORTLIST 33

## contains-await-cover
- spec: sec-static-semantics-contains (spec.html 9471-9482); sec-unary-operators (spec.html 20196)
- quote: For each child node _child_ of this Parse Node, do … If _child_ is an instance of _symbol_, return *true*.
- text: An `await` expression parses as UnaryExpression : CoverAwaitExpressionAndAwaitUsingDeclarationHead, and no Parse
  Node is an |AwaitExpression|. So the "Contains |AwaitExpression|" early errors never apply.
- decision: test262: Contains counts a node of that production as an |AwaitExpression|. The proposed text is a Contains
  row for it.
- scope: early errors and static semantics that use Contains on await.
- decided: user 2026-10-16 20:35 (briefs/handoff-coordinator.md: 'Erratum + issue draft'; the errata approval)
- covers:
  - erratum ContainsAwaitCover
- report: docs/spec-issues/35-contains-awaitexpression-cover.md

## sab-byte-length-store
- spec: sec-allocatesharedarraybuffer 9.c (spec.html 45906)
- quote: Perform SetValueInBuffer(_byteLengthBlock_, 0, ~biguint64~, ℤ(_byteLength_), *true*, ~seq-cst~).
- text: AllocateSharedArrayBuffer's growable branch passes _byteLengthBlock_, a Shared Data Block, to SetValueInBuffer,
  which takes an ArrayBuffer.
- decision: test262: the step appends a seq-cst WriteSharedMemory event of the length to the agent's Events Record, as
  SetValueInBuffer's shared branch does.
- scope: growable SharedArrayBuffers.
- decided: user 2026-10-16 20:47 (briefs/handoff-coordinator.md: 'Erratum + issue draft')
- covers:
  - erratum AllocateSharedArrayBufferByteLengthStore
- report: docs/spec-issues/43-allocatesharedarraybuffer-byte-length.md

## createintrinsics-async-argument
- spec: sec-createintrinsics 2 (spec.html 11857)
- quote: Set fields of _realmRecord_.[[Intrinsics]] with the values listed in
- text: CreateIntrinsics passes _async_ in CreateBuiltinFunction's 7th position, which is _prefix_: read literally,
  built-in async functions get [[Async]] false and no prefix; the creation order is unstated.
- decision: test262: _async_ in its own position and _prefix_ when the entry has one; objects first, then properties
  in the host's order. The literal (realm.emu's definition reading) passes _async_ as _prefix_ and stops where
  SetFunctionName concatenates it (stops= sec-setfunctionname@5.a under CreateBuiltinFunction).
- scope: realm creation.
- decided: coordinator 2026-10-15 (merge 05925872f round-p);
  user 2026-10-18 (#9410, U1: an erratum)
- covers:
  - reading definition-sec-createintrinsics-2
  - erratum CreateIntrinsicsAsyncArgument
- note: tests/run/errata_createintrinsics_async_argument.js (test262) and its _literal case (ecma-run prints `stop:
  erratum CreateIntrinsicsAsyncArgument`; L2's blame names the phrase, `sortError phrase:11 ?`).
- report: docs/spec-issues/33-createintrinsics-async-argument-position.md, SHORTLIST 4

## sort-comparator
- spec: sec-sortindexedproperties (spec.html 41353)
- quote: The notation _a_ <C _b_ means ℝ(_comparator_(_a_, _b_)) < 0
- text: The consistent-comparator definition applies ℝ to the comparator's result, and ℝ(±∞) is undefined, so the
  definition has no value for a comparator that returns ±∞: it is neither consistent nor inconsistent.
- decision: test262: an order that meets the conditions for every consistent comparator giving the observed results;
  else the host's. Both hosts' SortStep (RefHost, the Fast host: `sortStepBy`) is a stable binary insertion sort by the
  sign of the result (zeros and NaN equal). The literal (sort.emu's definition reading, `Let _order_ be ℝ(_result_)`)
  stops with a sort error on a ±∞ result; no stops= names it, since the step is inside a reading.
- scope: Array and TypedArray sort.
- decided: coordinator 2026-10-15 (merge 07ce0fb07 round-l);
  user 2026-10-18 (#9410, U1: an erratum)
- covers:
  - reading definition-sec-sortindexedproperties-4
  - host SortStep
  - erratum SortInfiniteComparator
- note: tests/run/errata_sort_infinite_comparator.js (test262) and its _literal case (`stop: sortError ? ?`).
- report: docs/spec-issues/31-sort-infinite-comparator.md

## unregister-iterates-cells
- spec: sec-finalization-registry.prototype.unregister 5 (spec.html 48509-48512)
- quote: _cell_ of _finalizationRegistry_.[[Cells]], do … Remove _cell_ from _finalizationRegistry_.[[Cells]].
- text: "For each Record ... _cell_ of _finalizationRegistry_.[[Cells]]" removes _cell_ from the List it iterates; the
  text does not say how a For each goes on over a List its body changes. The machine's For each goes by index over
  the List as it is at each round, so removing the current cell skips the next one (two cells with the token: one
  stays, and a second unregister returns *true*). No other loop of spec.html or the overlay changes its own List.
- decision: test262: the loop iterates a copy of [[Cells]] taken when it starts: each cell is tested once, every cell
  with the token is removed. The literal runs the general For each, which is left as it is; it never stops (stops="").
- scope: FinalizationRegistry.prototype.unregister.
- decided: coordinator 2026-10-17 (task t262-fail-finreg-unregister, coordinator #7217; confirmed in the decision log);
  user 2026-10-18 (#9410, U1: an erratum)
- covers:
  - erratum UnregisterIteratesCopy
- note: tests/run/errata_unregister_two_cells.js (`true|false`), its _literal case (`true|true`) and its _proposed
  case.
- report: docs/spec-issues/45-unregister-iterates-cells.md

## ischaracterclass-classcontrolletter
- spec: sec-regular-expressions-patterns (spec.html 53950); sec-patterns-static-semantics-early-errors-annexb
  (spec.html 53973-53975); sec-patterns-static-semantics-is-character-class-annexb (spec.html 53997-54006)
- quote: [~UnicodeMode] `c` ClassControlLetter … It is a Syntax Error if IsCharacterClass of the first |ClassAtom| is
  *true* … The semantics of IsCharacterClass is extended as follows:
- text: §B.1.2 adds `ClassEscape :: c ClassControlLetter`, §B.1.2.1's range rules ask IsCharacterClass of both ends,
  and neither §22.2.1.6 nor §B.1.2.3 defines it for that production (nor for ClassControlLetter or DecimalDigit):
  `/[\c1-\c5]/` has no early errors.
- decision: test262: §B.1.2.3 gets the row `1. Return *false*.` for the production, the twin of CharacterEscape's
  (the escape is one character; §B.1.2.4 gives its CharacterValue). The literal (no row) stops with a sort error at
  the range rules.
- scope: Annex B regular expression early errors (--web-browser).
- decided: user 2026-10-19 (#13017, option a of #12925: a model erratum, finding #12915)
- covers:
  - erratum IsCharacterClassControlLetter
- note: tests/run/frontend_regexp_annexb.js (`--web-browser`) expects `true false` for `/[\c1-\c5]/` and a
  SyntaxError for `[\c5-\c1]`; its run gets past the range rules and stops at the Contains residue every
  `--web-browser` run reaches. With `--erratum IsCharacterClassControlLetter=literal` it stops with a sortError at
  IsCharacterClass.
- report: docs/spec-issues/49-annexb-ischaracterclass-classcontrolletter.md, SHORTLIST 32

## races-not-both
- spec: sec-races 1.a (spec.html 53239)
- quote: If it is not the case that both _eventA_ happens-before _eventB_ in _execution_ and _eventB_ happens-before
  _eventA_ in _execution_, then
- text: "it is not the case that both A happens-before B and B happens-before A" is always true for a strict order.
- decision: Literal, an erratum that never stops (`stops=""`): the data and the memory model's meaning
  (Ecma.MemoryModel.Race) keep the literal condition, so two conflicting events race even when happens-before orders
  them. The erratum's note gives the proposed text ("If neither … nor …").
- scope: the memory model (multi-agent).
- decided: coordinator 2026-10-14 (merge c8e662201 docs-arc);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading; #11026)
- covers:
  - erratum RacesNotBoth
  - code Ecma.MemoryModel.Race
  - file docs/spec-issues/23-races-not-both.md
- report: docs/spec-issues/23-races-not-both.md, SHORTLIST 9

## child-of-through-unit-chain
- spec: sec-islabelledfunction 1-2 (spec.html 23312-23313); sec-parsing (spec.html 367);
  sec-algorithm-conventions-syntax-directed-operations (spec.html 747)
- quote: If _stmt_ is not a |LabelledStatement|, return *false*. … Let _item_ be the |LabelledItem| of _stmt_.
- text: IsLabelledFunction takes a |Statement| node, but step 1 tests whether it "is a |LabelledStatement|" and step
  2 takes "the |LabelledItem| of _stmt_": for `Statement : LabelledStatement` that is a grandchild, and §5.1.2
  gives a node only its right-hand side's children; the chain-production rule covers SDOs only. Literally, step 1
  is always false and `if (1) l: function f() {}` is valid (test262 labelled-fn-stmt*.js require a SyntaxError);
  the model reads `n is a |X|` through the unit chain, so its literal reading passes step 1 and stops at step 2.
- decision: Erratum UnitChainChild, at test262 by default: `the |X| of n` takes X from the first node of n's unit
  chain (strict unit productions) whose production has X (reading A); `n is a |X|` already matches through the
  unit chain. The literal reading takes X from n alone and stops (a sort error) where n's production has no X.
- scope: every `the |X| of n` site where n's own production has no X (nt-of and Expr.childOf); the chain starts at n
  itself.
- decided: user 2026-10-17 (part (b) reading A, relayed by the coordinator to esl-child-unit);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum UnitChainChild
  - file docs/spec-issues/36-islabelledfunction-labelleditem.md
  - code Ecma.Expr.childOf
- report: docs/spec-issues/36-islabelledfunction-labelleditem.md

## lookahead-reads-source-tokens
- spec: sec-lookahead-restrictions (spec.html 639-640); sec-rules-of-automatic-semicolon-insertion 1
  (spec.html 18069-18072)
- quote: is a prefix of the immediately following input token sequence. … then a semicolon is automatically inserted
  before the offending token
- text: A lookahead restriction reads "the immediately following input token sequence", and §12.10 inserts its
  semicolons "into the source code token stream": the text does not say whether an inserted semicolon is an input
  token a lookahead reads. Read as one, `if (0) let` LF `[a] = 0;` is a sentence: rule 1 inserts `;` before the
  offending `[`, and ExpressionStatement's [lookahead ∉ { `let` `[` }] then reads `let ;` (test262
  language/statements/*/let-array-with-newline.js require a SyntaxError).
- decision: Erratum LookaheadSourceTokens, at test262 by default: a lookahead restriction reads the source's
  tokens, past the semicolons §12.10 inserted (`Alphabet.look`, `tokenAlphabet`'s `pastVirt`; Parse.Syntax.look).
  The literal reading stops wherever a lookahead reads at an inserted `;`, including where both readings agree
  (Parse.Syntax.run's `lit`, `FastP.litLook`): ParseText stops there.
- scope: every lookahead restriction of the syntactic grammar; a lookahead sequence over an inserted `;`.
- decided: coordinator 2026-10-17 (bus #7348, #7355, task t262-fail-let-newline);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum LookaheadSourceTokens
  - code Ecma.Grammar.Alphabet.look
  - file docs/spec-issues/44-lookahead-source-tokens.md
- report: docs/spec-issues/44-lookahead-source-tokens.md

## stringvalue-reservedword
- spec: sec-identifiers-static-semantics-early-errors (spec.html 18337-18415); sec-static-semantics-stringvalue
  (spec.html 18417-18467)
- quote: It is a Syntax Error if the StringValue of |IdentifierName| is the StringValue of any |ReservedWord| except for
  `yield` or `await`.
- text: The rule takes the StringValue of a |ReservedWord|, which StringValue does not define.
- decision: Erratum StringValueReservedWord, at test262 by default: the StringValue of a terminal is the String of
  its code points, as test262 has it. The literal reading stops where the rule takes the StringValue of a
  |ReservedWord|.
- scope: Identifier early errors.
- decided: coordinator 2026-10-14 (merge c8e662201 docs-arc);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum StringValueReservedWord
  - overlay ph-stringvalue-any-nt-except
  - overlay ph-stringvalue-terminal-except
- report: docs/spec-issues/32-stringvalue-reservedword.md

## annexb-html-close-is-comment
- spec: sec-html-like-comments (spec.html 53811-53819); sec-lexical-and-regexp-grammars (spec.html 384)
- quote: Input elements other than white space and comments form the terminal symbols for the syntactic grammar for
  ECMAScript and are called ECMAScript tokens.
- text: B.1.1 adds HTMLCloseComment as its own alternative of InputElementHashbangOrRegExp, not under Comment; §5.1.3
  drops only white space and comments, so literally a first-line `-->` is a token no syntactic production has, and
  the Script has no parse (test262 single-line-html-close-first-line-{1,2,3}.js expect a comment).
- decision: Erratum HTMLCloseCommentToken, at test262 by default: an HTMLCloseComment input element is a comment
  (Element.isToken excludes it, lean/Ecma/Grammar/Derives.lean). The literal reading makes it a token, and the Script has no parse;
  the model stops on such a Script (Engine.litStop).
- scope: Annex B hosts, a Script's first input element.
- decided: coordinator 2026-10-18 (arc/plans/esl-annexb-parse.md M2, decision log; task esl-annexb-meaning-ctx);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum HTMLCloseCommentToken
  - file docs/spec-issues/41-annexb-html-close-comment-token.md
  - code Ecma.Grammar.Element.isToken
- report: docs/spec-issues/41-annexb-html-close-comment-token.md

## annexb-regexp-order
- spec: sec-regular-expressions-patterns (spec.html 53870); sec-regular-expressions-patterns (spec.html 53959)
- quote: When parsing using the following grammar, each alternative is considered only if previous production
  alternatives do not match.
- text: B.1.2's "each alternative is considered only if previous production alternatives do not match" is procedural
  and says neither what an alternative matches nor how nested choices combine. Without an order the grammar is
  ambiguous (`/a{1}/` one Term or four; `\b` an Assertion or an identity escape; `\1` a DecimalEscape or a
  LegacyOctalEscapeSequence). Read as priority among complete parses, a later alternative wins wherever an earlier
  one matched only a prefix: `/\b*/` parses as `b*`, which engines reject and upstream's reading excludes
  (tc39/ecma262 #2228, merged; #2445, open).
- decision: Erratum AnnexBRegExpOrder, at test262 by default; the literal reading stops on a pattern with more than
  one parse, and the model, which does not decide that, on every B.1.2 pattern (Engine.litStop). The test262 reading: commitment, for the nonterminals B.1.2 restates (GL.orderedNts: Term, Assertion, QuantifiableAssertion,
  ExtendedAtom, InvalidBracedQuantifier, ExtendedPatternCharacter, AtomEscape, CharacterEscape, IdentityEscape,
  SourceCharacterIdentityEscape, ClassAtomNoDash, ClassEscape, ClassControlLetter): a node of such an n at i uses
  alternative k (its position in GL.alts) only if no earlier alternative of n derives, in Derives with the group-number
  condition, any span from i (Ecma.Grammar.Tree.Commits, Committed, ParsesCode where GL.ordered). Alternative and
  Disjunction are §22.2.1's, not restated, so `[empty]` never preempts a Term. No rank order breaks ties.
- scope: Annex B hosts, RegExp patterns without the u or v flag.
- decided: coordinator 2026-10-18 (arc/plans/esl-annexb-parse.md M3, decision log);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum AnnexBRegExpOrder
  - file docs/spec-issues/40-annexb-regexp-order-group-count.md
- note: Commitment leaves one parse on the test cases (checked on them, not proved), and an earlier alternative's match read committed instead of in Derives gives the
  same parses there.
- report: docs/spec-issues/40-annexb-regexp-order-group-count.md

## annexb-group-number-stratified
- spec: sec-regular-expressions-patterns (spec.html 53919); sec-countleftcapturingparenswithin (spec.html
  37616-37632); sec-countleftcapturingparens-annexb (spec.html 53992-53995)
- quote: but only if the CapturingGroupNumber of |DecimalEscape| is ≤ CountLeftCapturingParensWithin(the |Pattern|
  containing |DecimalEscape|)
- text: AtomEscape's `[> but only if the CapturingGroupNumber of |DecimalEscape| is ≤
  CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)]` reads the Pattern whose parse the
  condition itself decides: the text gives no rule for finding that tree.
- decision: Erratum AnnexBGroupCount, at test262 by default; the literal reading stops on a pattern with more than
  one parse, and the model on every B.1.2 pattern with a `\` and a nonzero digit, where a DecimalEscape may read the
  condition (Engine.litStop). The test262 reading: stratified (Ecma.Grammar.groupCond, installed by ParsesCode): the count is CountLeftCapturingParensWithin
  (Atom's and ExtendedAtom's `( GroupSpecifier? Disjunction )` nodes) of a committed parse of the input as
  Pattern[~UnicodeMode, ~UnicodeSetsMode, ~NamedCaptureGroups] with the condition true.
- scope: Annex B hosts, RegExp patterns without the u or v flag.
- decided: coordinator 2026-10-18 (arc/plans/esl-annexb-parse.md M4, decision log; task esl-annexb-meaning-regexp);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum AnnexBGroupCount
  - file docs/spec-issues/40-annexb-regexp-order-group-count.md
- note: The count does not depend on the condition, on NamedCaptureGroups or on which committed parse with the
  condition true it is read from (checked on test cases; not
  proved, a hypothesis of the parser's soundness under Annex B).
- report: docs/spec-issues/40-annexb-regexp-order-group-count.md

## covered-node-in-tree
- spec: sec-isintailposition 2 (spec.html 25916); sec-mightbothparticipate 1 (spec.html 37358);
  sec-shallowestcontainedjsonvalue 6.d.i.2.a-6.d.ii.1 (spec.html 47778-47785); sec-syntactic-grammar
  (spec.html 370-410)
- quote: If _call_ is not contained within a |FunctionBody|, a |ConciseBody|, or an |AsyncConciseBody|, return *false*.
- text: §5.1.5 reparses a cover with _n_ as goal, so the covered node is the root of a separate tree: "contained
  within", "most closely contains" and "the parent of" fail for a node inside it (`return (f(n - 1))` is then no
  tail call, against test262 tco-pos.js).
- decision: Erratum CoveredNodeParent, at test262 by default: the covered node takes the cover's place in the tree,
  its parent being the cover's parent (NearestEnclosing, Parent, ParseNodesWithin, ChildNodes). The literal reading
  keeps the covered node the root of its own tree; the model stops at a cover's reparse under it
  (Engine.litStop).
- scope: every Parse Node query that starts inside a cover.
- decided: coordinator 2026-10-14 (merges 37db21bb9 round-a, 46a83f4ac round-b, d3bbe5409 round-c, aee638fcb round-d);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum CoveredNodeParent
  - reading definition-sec-isintailposition-2
  - reading definition-sec-mightbothparticipate-1
  - reading definition-sec-shallowestcontainedjsonvalue-6.d.i.2.a
  - reading definition-sec-shallowestcontainedjsonvalue-6.d.i.3.a
  - reading definition-sec-shallowestcontainedjsonvalue-6.d.ii.1
  - overlay prim-nearestenclosing
- note: docs/spec-issues/19-other-questions.md 19.3 (the goal symbol per parse) is a related question, not filed.
- report: docs/spec-issues/46-covered-node-parent.md

## annexb-modifiers-early-errors
- spec: sec-patterns-static-semantics-early-errors-annexb (spec.html 53962-53990)
- quote: the rules for the following productions are modified with the addition of the highlighted text
- text: §B.1.2's grammar loses §22.2.1.1's modifier early errors (`/(?ii:a)/`).
- decision: Erratum AnnexBModifierEarlyErrors, at test262 by default: no Annex B modifier rule, the main grammar's
  five modifier rules apply to B.1.2's two ExtendedAtom modifier productions (each a rule reading with `also=`,
  whose twin row has an empty literal body). The literal reading applies none, and `/(?ii:a)/` is valid.
- scope: Annex B RegExp patterns.
- decided: coordinator 2026-10-14 (merge c8e662201 docs-arc);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading)
- covers:
  - erratum AnnexBModifierEarlyErrors
  - file docs/spec-issues/26-annexb-modifiers-early-errors.md
- report: docs/spec-issues/26-annexb-modifiers-early-errors.md

## mv-decimalintegerliteral-zero
- spec: sec-literals-numeric-literals (spec.html 17115-17118); sec-static-semantics-mv (spec.html 17235)
- quote: The MV of DecimalIntegerLiteral :: `0` is 0.
- text: PR #3988 (78ea84c0) made |DecimalIntegerLiteral|'s first alternative |DecimalDigit| and removed
  `DecimalIntegerLiteral :: `0``, but left its MV row: the row names a production the grammar does not have.
- decision: Literal: the row is kept with no production, so it is never applied (the MV of `0` is its
  |DecimalDigit|'s through the chain production, 0); the proposed text deletes the row. Both readings give the same
  result, so nothing switches. The generators report the row as this erratum and stop on any other row whose
  production the grammar does not have.
- scope: the numeric literal `0`.
- decided: user 2026-11-18 (F1b: a new erratum, with a write-up)
- covers:
  - erratum MVDecimalIntegerLiteralZero
- report: docs/spec-issues/52-mv-decimalintegerliteral-zero.md

# Proposed normative changes

## bigint-maximum-size
- spec: sec-ecmascript-language-types-bigint-type (spec.html 2222); sec-numeric-types-bigint-exponentiate 3;
  sec-numeric-types-bigint-multiply 1; sec-numeric-types-bigint-add 1; sec-numeric-types-bigint-subtract 1;
  sec-numeric-types-bigint-leftShift 2; sec-bigint.asuintn 3
- quote: The value may be any size and is not limited to a particular bit-width.
- text: BigInt::exponentiate, BigInt::leftShift, BigInt::multiply, BigInt::add, BigInt::subtract, and BigInt.asUintN
  return their exact results whatever their size; every implementation has a maximum BigInt size and throws a
  *RangeError* past it (V8 at 2^30 bits).
- decision: Proposed reading (resolution `proposed`, kind `proposal`), switchable: before each of the six forms its
  result, "If the result would exceed the implementation's maximum BigInt size, throw a *RangeError* exception";
  the host says whether it would (BigIntTooLarge; the engine's limit 2^30 bits, preserving the `asUintN` fast path
  when non-negative _bigint_ already fits). Read literally, the result is formed whatever its size, and an
  implementation gives up at a limit of its own.
- scope: BigInt exponentiation, left shift, multiplication, addition, subtraction, and asUintN with huge results.
- decided: user 2026-11-18 (stage 4: a switchable reading; F2: a proposal, not a defect); extended Step 4C 2026-11-20
- covers:
  - erratum BigIntMaximumSize
- report: docs/spec-issues/51-bigint-maximum-size.md

## string-maximum-length
- spec: sec-ecmascript-language-types-string-type; sec-string.prototype.repeat 7; sec-stringpaddingbuiltinsimpl 7;
  sec-string.prototype.concat 5.b; sec-applystringornumericbinaryoperator 1.c.iii; sec-joinindexedproperties 4.a, 4.d.iii
- quote: The String type is the set of all ordered sequences of zero or more 16-bit unsigned integer values (“elements”) up to a maximum length of 2<sup>53</sup> - 1 elements.
- text: ECMA-262 specifies Strings up to length 2^53 - 1 and leaves implementations' smaller maximum String lengths
  unspecified; String.prototype.repeat, StringPaddingBuiltinsImpl, String.prototype.concat, string `+`, and
  JoinIndexedProperties produce unboundedly long Strings under the literal reading.
- decision: Proposed reading (resolution `proposed`, kind `defect`), switchable: check StringTooLarge before constructing
  the resulting String (after checking non-empty _fillString_ in StringPaddingBuiltinsImpl), throwing *RangeError*
  when *true*. The engine's host (`maxStringLength := 2^28 = 268435456`) answers `StringTooLarge`.
- scope: String-growing operations exceeding an implementation's maximum String length.
- decided: user 2026-11-20 (Step 4C)
- covers:
  - erratum StringMaximumLength
- report: docs/spec-issues/53-string-maximum-length.md

# Interpreting readings

## early-errors-cover-first
- spec: sec-syntactic-grammar (spec.html 401-410); sec-static-semantic-rules (spec.html 883); sec-parsetext 2-5
  (spec.html 16439-16442); sec-arrow-function-definitions-static-semantics-early-errors (spec.html 24081-24097);
  sec-async-arrow-function-definitions-static-semantics-early-errors (spec.html 25808-25812)
- quote: |CoverCallExpressionAndAsyncArrowHead| must cover an |AsyncArrowHead|.
- text: When a cover does not cover the nonterminal a rule says it must, the other rules of that production and of
  the productions above it still apply, and their conditions read static semantics through the cover (Contains,
  BoundNames, IsSimpleParameterList), whose rows take "the |n| that is covered by" it: a node that does not exist
  (`([...x = []]) => {}`, `async (...x = []) => {}`). The text orders no rules and skips none.
- decision: Option A, in two halves. (1) EarlyErrorsOf applies a node's rules only when the nodes it contains have
  no early errors. (2) Early Errors of a node applies its own "must cover" rules first, and its other rules only
  when those report none (AsyncArrowFunction's rules beside its own cover rule); a covered node's rules are applied
  as EarlyErrorsOf applies them. The List is then not every early error, but it is non-empty exactly when there is
  one. Not an erratum: a cover that fails its "must cover" rule already makes the program an early SyntaxError, and
  ParseText leaves the number and order of the errors implementation-defined, so no program's result depends on
  the order; the reading takes the one order in which no rule reads through a cover that covers nothing.
- scope: every early-error check (ParseTextIn); it changes results only where the literal reading stops.
- decided: coordinator 2026-10-18 (option A; bus #8551, #8578);
  user 2026-10-18 (#9410, U1: an erratum, run at its current reading); user 2026-11-18 (F2, the errata review: not
  an erratum, a reading)
- covers:
  - overlay formal-earlyerrorsof
  - overlay formal-early-errors-cover-rules-first
  - code Ecma.Machine.linOwn
  - overlay formal-early-errors-cover-rules-first
  - file docs/spec-issues/39-must-cover-other-rules.md
- note: Dependent: reading row-propname-coverinitializedname, whose stops="" holds by half (1) (row
  propname-coverinitializedname); a change to (1) revisits it.
- report: docs/spec-issues/39-must-cover-other-rules.md

## propname-coverinitializedname
- spec: sec-static-semantics-propname (spec.html 10111-10195)
- quote: PropName ( ): a String or ~empty~
- text: PropName has no row for CoverInitializedName, and PropertyNameList asks for it.
- decision: The row of the shorthand IdentifierReference twin (syntax.emu); no answer depends on it, so it is a
  reading, not an erratum. The missing row is never asked: under early-errors-cover-first the ObjectLiteral's `__proto__` rule, PropertyNameList's only asker,
  applies only when the nodes it contains have no early error, and a CoverInitializedName always has one.
- scope: ObjectLiteral early errors.
- decided: coordinator 2026-10-13 (merge 3e638231f c3-round);
  user 2026-10-18 (#9410, U1: an erratum); user 2026-11-18 (F2, the errata review: not an erratum, a reading)
- covers:
  - reading row-propname-coverinitializedname
- note: tests/run/errata_propname_cover_initialized_name.js: `normal: "SyntaxError"`.
- report: docs/spec-issues/29-propname-coverinitializedname.md, SHORTLIST 19

## annexb-regexp-extension
- spec: sec-patterns-static-semantics-early-errors-annexb (spec.html 53971); sec-compiletocharset-annexb (spec.html
  54232-54233); sec-compiletocharset-annexb (spec.html 54082); sec-parsepattern-annexb (spec.html 54118);
  sec-countleftcapturingparens-annexb (spec.html 53994); sec-compilesubpattern-annexb (spec.html 54032-54034);
  sec-compileatom-annexb (spec.html 54047)
- quote: the rules for the following productions are modified with the addition of the highlighted text … The
  semantics of CompileToCharSet with argument _regexpRecord_ is extended as follows: … Two rules are
  replaced: … The following rules are also added: … is extended as follows, with modifications highlighted
- text: B.1.2's clauses extend operations of §22.2 ("is extended as follows"), add rules, replace two rules, modify
  two productions' early rules and give ParsePattern a modified body, while the annex is optional off a web
  browser: the text says neither how the extended and the plain operation stand in one specification nor that the
  choice holds for the whole run.
- decision: An annex row on a production without a main row of its SDO (B.1.2's added rules, B.3.5's rows) is a
  row of the SDO (Ecma.SdoRow.annex), reached only where the annex grammar parsed. A replaced rule (CompileToCharSet
  on NonemptyClassRanges and NonemptyClassRangesNoDash) and ParsePattern's modified body are reached through overlay
  step patches (spec/formal/annexb.emu) on the main algorithms: a first step "if the host is a web browser or
  otherwise supports B.1.2", asking the host about sec-regular-expressions-patterns as the parse does, under which
  the annex row's steps run (CompileToCharSet) or the annex algorithm is returned (ParsePattern); off it the main
  steps run, and the annex CompileToCharSet rows stay shadowed (Ecma.SdoRow.mainLast). B.1.2.1's modified early rules
  stand for the main rules of their productions (Ecma.EarlyRow.modifies); their highlighted conditions apply on a
  B.1.2 host only, so off it they are the main rules. The answer is a fact of the run (Ecma.Host.OptionalLaws.webBrowser): the
  same at every call with the same arguments, the state unchanged.
  B.1.2.5-B.1.2.7's prose rules ("the same as … with |X| substituted for |Atom|") are overlay row readings
  (annexb.emu) on productions only the B.1.2 grammar has, so the ParsePattern gate is theirs too. B.1.2.2's
  reinterpreted references in CountLeftCapturingParensWithin and CountLeftCapturingParensBefore are definition
  readings counting |Atom|'s and |ExtendedAtom|'s group nodes with no host query: off a B.1.2 host no |ExtendedAtom|
  node exists, so the count is the main text's.
- scope: Annex B hosts, B.1.2.
- decided: user 2026-10-18 (#10629, route C: no printer change, the gate as an overlay step patch; coordinator
  #10659); B.1.2.2's readings without a host query: coordinator 2026-10-19, reviewed (review-esl-annexb-regexp-subst)
- covers:
  - reading definition-sec-countleftcapturingparenswithin-2
  - reading definition-sec-countleftcapturingparensbefore-3
  - code Ecma.SdoRow.annex
  - code Ecma.SdoRow.mainLast
  - code Ecma.Src.rowMap
  - code Ecma.Src.earlyMap
  - code Ecma.EarlyRow.modifies
  - code Ecma.Host.OptionalLaws.webBrowser
  - file spec/formal/annexb.emu
- report: -

## annexb-quantifiableassertion-compile
- spec: sec-compilesubpattern-annexb (spec.html 54032); sec-compilesubpattern (spec.html 37962-37964);
  sec-compileassertion-annexb (spec.html 54040-54041)
- quote: is the same as for Term :: Atom Quantifier but with |QuantifiableAssertion| substituted for |Atom|
- text: Term :: Atom Quantifier's first step is "Let _m_ be CompileAtom of |Atom| with arguments _regexpRecord_ and
  _direction_". Substituting |QuantifiableAssertion| for |Atom| in it asks CompileAtom of a |QuantifiableAssertion|,
  for which CompileAtom has no rule (the chain falls to |Disjunction| and stops), while B.1.2.6 gives
  |QuantifiableAssertion| CompileAssertion rules. "Substituted" is not defined.
- decision: The substitution takes the operation of the substituted nonterminal's rules with it: _m_ is
  CompileAssertion of |QuantifiableAssertion| with argument _regexpRecord_ (CompileAssertion takes no _direction_,
  as Term :: Assertion's rule shows); the other steps substitute |QuantifiableAssertion| for |Atom|.
- scope: Annex B hosts, a quantified lookahead (`/(?=a)*/`) in a pattern without the u or v flag.
- decided: coordinator 2026-10-19 (interpreting reading, not an erratum; task esl-annexb-regexp-subst)
- covers:
  - reading row-compilesubpattern-quantifiableassertion-quantifier
- note: test262 annexB/language/literals/regexp quantifiable-assertion cases and every engine compile a quantified
  lookahead as the lookahead repeated.
- report: -

## makeday-time-value-range
- spec: sec-makeday 8 (spec.html 34380)
- quote: Find a finite time value _tv_ such that YearFromTime(_tv_) = ℝ(_balancedYear_)
- text: "Find a finite time value _tv_ such that …" leaves open whether "time value" is the definition (any finite
  integral Number) or the ±8.64 × 10^15 range.
- decision: The definition. The callers' TimeClip applies the range, as the three engines do. The Find fixes only
  Day(_tv_): every _tv_ that meets it has Day(_tv_) = DayFromYear(_balancedYear_) + the month's start, and step 9
  reads only Day(_tv_). FirstDayOf answers the least such _tv_ (a choice the text leaves open, unobservable), and
  NaN exactly when none exists.
- scope: Date arithmetic near the range bounds.
- decided: coordinator 2026-10-18 (arc/plans/readings-audit.md §3); user 2026-10-18 (#9410, U3); coordinator
  2026-10-23 (#22908, the Day reading)
- covers:
  - reading definition-sec-makeday-8
  - code Ecma.Prims.Date.firstDayOf
- note: At Ref: one Day, and firstDayOf_law (the least, or NaN and none).
- report: SHORTLIST 16

## native-function-empty-initial-name
- spec: sec-function.prototype.tostring 3 (spec.html 31669)
- quote: if _func_ has an [[InitialName]] internal slot and _func_.[[InitialName]] is a String, the portion of
- text: For an empty [[InitialName]], the step asks that the portion matched by NativeFunctionAccessor? PropertyName
  be the empty String; a NativeFunction without a PropertyName has no such portion.
- decision: The portion of a NativeFunction without a NativeFunctionAccessor or a PropertyName is empty, so an empty
  [[InitialName]] is met by one (`function () { [native code] }`): step 3 answers NativeFunctionSource, whose law then
  asks for such a String. Any other [[InitialName]] meets it when it is `get` or `set` (the NativeFunction is ambiguous;
  either way the portion is the name), or when `function `, it and `() { [native code] }` parse as a NativeFunction
  whose NativeFunctionAccessor? PropertyName portion is all of it. The erratum NativeFunctionInitialName (row
  native-function-initial-name) covers the names no String meets.
- scope: Function.prototype.toString of built-ins with an empty or unusual [[InitialName]] (anonymous built-ins).
- decided: coordinator 2026-10-17 (bus #5154, esl-fpts-step3; the empty case and get/set: review of esl-fpts-step3
  @5208f4d82, D1 and N1)
- covers:
  - reading definition-sec-function.prototype.tostring-3
- report: -

## parse-node-contains
- spec: sec-groupspecifiersthatmatch 4 (spec.html 37716); sec-mightbothparticipate 2 (spec.html 37359);
  sec-countleftcapturingparenswithin (spec.html 37324); sec-countleftcapturingparensbefore (spec.html 37344);
  sec-patterns-static-semantics-early-errors (spec.html 37181); sec-parsetimezoneoffsetstring (spec.html 34692);
  sec-continue-statement-static-semantics-early-errors (spec.html 22971); sec-break-statement-static-semantics-early-errors
  (spec.html 23004); sec-regexpbuiltinexec (spec.html 39852)
- quote: Parse Nodes contained within _parseNode_. … not nested, directly or indirectly (but not crossing function or
  `static` initialization block boundaries), within an |IterationStatement|. … If _regexp_ contains any |GroupName|,
  then
- text: "contained within" / "contain" for Parse Nodes and "the derived |X|" (12 uses) are never defined; nor are
  "occur before", "nested, directly or indirectly (but not crossing function … boundaries), within", or what a
  RegExp object "contains".
- decision: A node is contained within another when it is that node or a node it contains (reflexive descendant):
  "the |X| Parse Node(s) contained within _n_" search _n_ too; "_x_ is contained within a |X|" and "_n_ contains a
  |X|" exclude the node itself. A node occurs before _a_ when it precedes _a_ in source order (a node before its
  children) and does not contain it. Nesting stops at the nearest |FunctionBody| or |ClassStaticBlockBody|. A RegExp
  instance contains what its |Pattern| contains. The derived |Disjunction| is the one the step names;
  GroupSpecifiersThatMatch lists them in source order.
- scope: Parse Node containment in early errors and static semantics; RegExpBuiltinExec's group names.
- decided: coordinator 2026-10-14 (merges d161b3751 c3-b14, 37db21bb9 round-a, d3bbe5409 round-c, 754fb5f20 round-g,
  58029fb3c round-j)
- covers:
  - reading definition-sec-groupspecifiersthatmatch-4
  - reading definition-sec-mightbothparticipate-2
  - overlay ph-contained-within
  - overlay ph-contains-node
  - overlay ph-not-contains-node
  - overlay ph-not-contains-two-nodes
  - overlay ph-node-within
  - overlay ph-first-node-within
  - overlay ph-second-node-within
  - overlay ph-count-nodes-within
  - overlay ph-count-nodes-before
  - overlay ph-two-distinct
  - overlay ph-contains-any-nt
  - overlay ph-not-nested
  - overlay ph-not-nested-alt
- report: SHORTLIST 19

## catch-env-created-for
- spec: sec-runtime-semantics-catchclauseevaluation 2 (spec.html 23461); sec-evaldeclarationinstantiation
  (spec.html 30246-30293)
- quote: Let _catchEnv_ be NewDeclarativeEnvironment(_oldEnv_). … If _thisEnv_ is not the Environment Record for a
  |Catch| clause, throw a *SyntaxError* exception.
- text: "the Environment Record for a |Catch| clause" is read elsewhere, but nothing records which Catch an
  environment is for.
- decision: The step also records the Catch (a [[CreatedFor]] field) that _catchEnv_ is for; "is not the Environment
  Record for a |Catch| clause" tests that field.
- scope: Annex B catch-parameter redeclaration.
- decided: coordinator 2026-10-15 (merge 07ce0fb07 round-l)
- covers:
  - reading definition-sec-runtime-semantics-catchclauseevaluation-2
  - overlay ph-not-env-for
- report: -

## forin-iterator-host-model
- spec: sec-enumerate-object-properties 1 (spec.html 22780)
- quote: Return an iterator object whose `next` method iterates over all the String-valued keys of enumerable properties
  of _obj_. The iterator object is never directly accessible to ECMAScript code.
- text: EnumerateObjectProperties returns an implementation-defined iterator, constrained by prose rules on
  properties and their order.
- decision: A closure whose internal method calls the host chooses (ForInStep); [[Prototype]], throw and return are
  unobservable and absent; an abrupt call is returned from `next`.
- scope: for-in.
- decided: coordinator 2026-10-15 (merge 07ce0fb07 round-l)
- covers:
  - reading definition-sec-enumerate-object-properties-1
- report: -

## json-parse-any-realm
- spec: sec-shallowestcontainedjsonvalue 2 (spec.html 47766)
- quote: Assert: _activeFunc_ is a `JSON.parse` built-in function object
- text: "%JSON.parse%" names the intrinsic of one realm; the step tests whether a function is JSON.parse.
- decision: A JSON.parse built-in of any realm (its behaviour is the algorithm of JSON.parse).
- scope: JSON.parse source text access.
- decided: coordinator 2026-10-16 (merge 4697e3a5f round-r)
- covers:
  - reading definition-sec-shallowestcontainedjsonvalue-2
- report: -

## assert-wording
- spec: sec-getmodulenamespace 1 (spec.html 29324); sec-resolveexport 7.a (spec.html 28849); sec-getwaiterlist 1
  (spec.html 46931); sec-addrestrictedfunctionproperties 1 (spec.html 13747)
- quote: is not ~new~ or ~unlinked~. … was not explicitly defined by this module. … are valid byte offsets within the
  memory of _block_. … exists and has been initialized.
- text: Asserts in undefined terms: "is not ~new~ or ~unlinked~", "explicitly defined", "valid byte offsets within
  the memory of", "has been initialized" (of an Intrinsics field, which has no initialized state).
- decision: Neither value; an ExportEntry of [[LocalExportEntries]] or [[IndirectExportEntries]] with that name; an
  index of one of the block's bytes; the field exists and is an Object.
- scope: those Asserts.
- decided: coordinator 2026-10-13 (merge 77203c098 c3-asserts)
- covers:
  - reading definition-sec-getmodulenamespace-1
  - reading definition-sec-resolveexport-7.a
  - phrase ph-not-explicitly-defined-export
  - reading definition-sec-getwaiterlist-1
  - reading definition-sec-addrestrictedfunctionproperties-1
- report: SHORTLIST 19

## number-shift-width
- spec: sec-numeric-types-number-leftShift 4 (spec.html 1952); sec-numeric-types-number-signedRightShift 4
  (spec.html 1969); sec-numeric-types-number-unsignedRightShift 4 (spec.html 1986); sec-numeric-types-number-bitwiseNOT
  2 (spec.html 1738)
- quote: Return the result of left shifting _leftNumber_ by _shiftCount_ bits. The mathematical value of the result is
  exactly representable as a 32-bit two's complement bit string.
- text: "the result of left shifting _x_ by _n_ bits" is an informal operation; its width comes only from a range
  sentence.
- decision: Arithmetic on the 32-bit view: ToFixedSizeInteger(x × 2^n) for left shift, floor(x / 2^n) for the right
  shifts, -x - 1 for NOT.
- scope: Number shift and NOT operators.
- decided: coordinator 2026-10-13 (merge f51b52fdf residue)
- covers:
  - reading definition-sec-numeric-types-number-leftShift-4
  - reading definition-sec-numeric-types-number-signedRightShift-4
  - reading definition-sec-numeric-types-number-unsignedRightShift-4
  - reading definition-sec-numeric-types-number-bitwiseNOT-2
- report: docs/spec-issues/25-number-shift-result.md, SHORTLIST 12

## parseint-radix-digit
- spec: sec-parseint-string-radix 11 (spec.html 30422)
- quote: If _trimmedString_ contains a code unit that is not a radix-_radixMV_ digit
- text: "a radix-_R_ digit" is only implied by step 14's letter values.
- decision: A code unit whose RadixDigitValue is below the radix.
- scope: parseInt.
- decided: coordinator 2026-10-13 (merge b6d1bba88 parseint)
- covers:
  - reading definition-sec-parseint-string-radix-11
- report: SHORTLIST 19

## parseint-significant-digits
- spec: sec-parseint-string-radix 14 (spec.html 30425)
- quote: contains more than 20 significant digits, every significant digit after the 20th may be replaced by a 0 digit
- text: The parenthesis allows replacing "every significant digit after the 20th" by 0 and, in other radices, an
  approximation: two latitudes.
- decision: One implementation-defined choice (truncation after 20 digits; every partial replacement gives the same
  Number); in other radices the host approximates.
- scope: parseInt of long numerals.
- decided: coordinator 2026-10-13 (merge b6d1bba88 parseint)
- covers:
  - reading definition-sec-parseint-string-radix-14
- report: -

## number-tostring-last-digit
- spec: sec-numeric-types-number-tostring 5 (spec.html 2154); sec-number.prototype.toexponential 11.b.i
  (spec.html 32761)
- quote: and _k_ is as small as possible. … and _ff_ is as small as possible.
- text: When several digit strings meet the condition, the last digit is left undetermined: implementation-defined
  or free per call is not said. The step's note is inexact: the criteria fix _k_ only, not _n_ or _s_ (radix 10,
  _x_ = 2<sup>-1073</sup>: 8e-324, 9e-324 and 1e-323 all meet them with _k_ = 1), so the choice is of _n_ and _s_.
- decision: The integers are the implementation's function of the Number and the radix, the same at every call: the
  model's `numDigits`, read by the primitives NumberDigitsExponent, NumberDigitsCount and NumberDigitsSignificand,
  with the step's condition and _k_ least as its law (`Model.NumLaws.numDigits_least`); toExponential's step is
  the same function at radix 10. The engine takes, of the tuples with the least _k_, the one with _s_ ×
  _radix_<sup>_n_ - _k_</sup> closest to ℝ(_x_), the even _s_ on a tie (the step's NOTE's rule). Nothing is asked
  of the host or logged.
- scope: Number::toString and toExponential.
- decided: coordinator 2026-10-13 (merge fcd89bda0 lst-readings); restated coordinator 2026-10-19 (ma-choices-m7);
  a function of the model, not a choice per call: user 2026-11-19 (stage 5e brief, review item 3)
- covers:
  - reading definition-sec-numeric-types-number-tostring-5
  - reading definition-sec-number.prototype.toexponential-11.b.i
  - code Ecma.Prims.Numbers.numberDigits
  - code Ecma.Model.numDigits
- report: SHORTLIST 18

## performeval-substep-order
- spec: sec-performeval 12 (spec.html 30127)
- quote: Perform the following substeps in an implementation-defined order, possibly interleaving parsing and error
  detection:
- text: The order of the substeps is implementation-defined.
- decision: The written order; every order is observably the same.
- scope: direct and indirect eval.
- decided: coordinator 2026-10-13 (merge a50833e00 choice)
- covers:
  - reading definition-sec-performeval-12
- report: -

## parse-context
- spec: sec-parsetext 2 (spec.html 16439); sec-ParseJSON 3 (spec.html 47587); sec-performeval 12 (spec.html 30127);
  sec-scripts-static-semantics-early-errors (spec.html 26313-26328)
- quote: Attempt to parse _sourceText_ using _goalSymbol_ as the goal symbol … unless the source text containing `super`
  is eval code that is being processed by a direct eval.
- text: Early-error rules depend on "being parsed for ParseJSON", on eval's context and on whether the parse is of
  eval code being processed by a direct eval, which ParseText's signature does not carry.
- decision: ParseText parses with no outside context; PerformEval and ParseJSON call ParseTextIn with theirs.
  ParseGoal and ParseTextIn carry _direct_, a Boolean; PerformEval passes whether its _direct_ is ~direct-eval~.
- scope: eval and JSON.parse parsing.
- decided: coordinator 2026-10-13 (merges d118e739d esl-ptext, 3e638231f c3-round); coordinator 2026-10-17
  (round-w, esl-direct-eval-parse review finding 1)
- covers:
  - reading definition-sec-parsetext-2
  - reading definition-sec-ParseJSON-3
  - reading definition-sec-performeval-12
- report: -

## canonical-property-value-column
- spec: sec-runtime-semantics-unicodematchpropertyvalue-p-v 3 (spec.html 39060)
- quote: Let _value_ be the canonical property value of _v_ as given in the “Canonical property value” column of the
  corresponding row.
- text: "the canonical property value of _v_ as given in the “Canonical property value” column of the corresponding
  row": no table of the clause and no UCD file has a column of that name.
- decision: The canonical property value is the long name of the PropertyValueAliases.txt row for _p_ that lists _v_
  (CanonicalPropertyValue). No result depends on the choice: the value only feeds PropertyCharSet, which accepts any
  alias of it.
- scope: UnicodeMatchPropertyValue, the \p{...} and \P{...} property escapes.
- decided: coordinator 2026-10-17 (bus #6786, #6827)
- covers:
  - reading definition-sec-runtime-semantics-unicodematchpropertyvalue-p-v-3
- report: -

## hostloadimportedmodule-each-time
- spec: sec-HostLoadImportedModule (spec.html 29219-29237)
- quote: then it must perform FinishLoadingImportedModule(_referrer_, _moduleRequest_, _payload_, _result_) with the
  same _result_ each time.
- text: "each time" does not say whether it covers the calls made before the first one that performed a normal
  completion, which may have performed a throw completion.
- decision: "each time" is every call: a host that once finishes a (referrer, request) pair with a normal completion
  finishes every call for an equal pair with that same result.
- scope: HostLoadImportedModule's requirements, every host; the test host's module map (row test-host-module-loader).
- decided: coordinator 2026-10-14 (merge c8e662201 docs-arc)
- covers:
- report: docs/spec-issues/19-other-questions.md (19.2: to SHORTLIST 19)

## suspendthisagent-combined-suspend
- spec: sec-suspendthisagent 7 (spec.html 47050); sec-notifywaiter (spec.html 47056-47061)
- quote: Perform LeaveCriticalSection(_waiterList_) and suspend the surrounding agent until the time is
  _waiterRecord_.[[TimeoutTime]], performing the combined operation in such a way that a notification that arrives
  after the critical section is exited but before the suspension takes effect is not lost. … another agent calling
  NotifyWaiter with arguments _waiterList_ and _thisAgent_ … _waiterRecord_: a Waiter Record,
- text: Step 7 is one prose step for two operations, LeaveCriticalSection and a suspension the text does not define,
  performed as one so that no notification is lost; its wake condition calls NotifyWaiter with an agent signifier,
  whose second parameter is a Waiter Record (upstream #3328).
- decision: Definition reading: LeaveCriticalSection(_waiterList_), then the host primitive
  SuspendAgentUntil(_waiterList_, _waiterRecord_.[[TimeoutTime]]), which carries the suspension, its atomicity with
  the LeaveCriticalSection before it, and the wake: by the timeout, or by NotifyWaiter(_waiterList_, _w_) for a Waiter
  Record _w_ whose [[AgentSignifier]] is the surrounding agent's (#3328 read as the Waiter Record of _thisAgent_).
  With one agent both readings of #3328 agree: nothing notifies, so the agent wakes only by the timeout.
- scope: Atomics.wait in ~sync~ mode on an agent that can block (DoWait 28.a).
- decided: coordinator 2026-10-18 (task esl-canblock-host, briefs/handoff-round-20.md; for review)
- covers:
  - reading definition-sec-suspendthisagent-7
- report: upstream tc39/ecma262#3328 (open on 2026-11-19)

## notifywaiter-wake-agent
- spec: sec-notifywaiter 2.a (spec.html 47068); sec-suspendthisagent 7 (spec.html 47050)
- quote: Wake the agent whose signifier is _waiterRecord_.[[AgentSignifier]] from suspension. … The surrounding agent
  can only wake from suspension due to a timeout or due to another agent calling NotifyWaiter
- text: Step 2.a wakes another agent from a suspension the text does not define (SuspendThisAgent step 7's prose), so
  what the wake does, and how the suspended agent observes it, is not said.
- decision: Definition reading: the host primitive WakeAgent(_waiterRecord_.[[AgentSignifier]]), logged. It wakes the
  agent of that signifier from its latest SuspendAgentUntil if it comes after it in the log, which AgentWoken reads,
  so a notification after the LeaveCriticalSection of step 7 is not lost. The suspended agent resumes in step 7's
  `Repeat, while AgentWoken() is *false*` loop, as 2.b's note says.
- scope: Atomics.notify of a ~blocking~ waiter.
- decided: coordinator 2026-10-20 (#16384, arc/plans/esl-agents.md D-2; for review)
- covers:
  - reading definition-sec-notifywaiter-2.a
- report: -

## b33-as-if-reparse
- spec: sec-functiondeclarations-in-ifstatement-statement-clauses (spec.html 54599)
- quote: Source text matched by this production is processed as if each matching occurrence of
  |FunctionDeclaration[?Yield, ?Await, ~Default]| was the sole |StatementListItem| of a |BlockStatement| occupying
  that position in the source text.
- text: "processed as if" is not defined: B.3.3 gives its |IfStatement| productions no rules of their own, and the
  text does not say which node the static and runtime semantics read in their place.
- decision: A node of B.3.3's productions is processed as the |IfStatement| that a reparse of its source text with
  `{` before and `}` after each |FunctionDeclaration| child gives (the phrase "the |X| that {A} is processed as",
  CoveredBy's reparse): a new parser invocation in the node's context, once per node, its root's parent the node's
  parent. Rows on B.3.3's productions read that |IfStatement| for every SDO with a rule for |IfStatement|
  (Evaluation, HasCallInTailPosition, VarDeclaredNames, VarScopedDeclarations, ContainsDuplicateLabels,
  ContainsUndefinedBreakTarget, ContainsUndefinedContinueTarget) and for Contains; EarlyErrorsOf descends into it
  in place of the node's own children, and so does B.3.2's walk ("For each |FunctionDeclaration| _f_ that is
  directly contained in the |StatementList| of a |Block|, ...", ph-annexb-foreach), through
  ParseNodesWithinProcessed, so that it finds the |FunctionDeclaration| of `if (x) function f(){}` in the
  |StatementList| of the processed-as |Block|. ParseNodesWithin itself keeps the parse's own nodes; its other
  readers never meet the processed-as |IfStatement| or do not depend on it: ph-count-nodes-within/-before
  (CountLeftCapturingParensWithin/Before), ph-two-distinct (Pattern early errors), ph-contains-any-nt
  (RegExpBuiltinExec), CaptureGroupName, MightBothParticipate and GroupSpecifiersThatMatch walk a |Pattern|,
  whose grammar has no |Statement|; ph-node-within, ph-first/second-node-within, ph-contains-node,
  ph-not-contains-node and ph-not-contains-two-nodes in ParseTimeZoneOffsetString walk a |UTCOffset|-family
  parse (no |Statement|); ShallowestContainedJSONValue walks ParseJSON's |Script|, valid JSON text with no
  statement in it; ParenthesizedOperandIsError's first |CoverParenthesizedExpressionAndArrowParameterList| is
  its operand's unit chain, before any statement in preorder; Function.prototype.toString's readings (a
  |NativeFunction|) seek |PropertyName| and |NativeFunctionAccessor| and read only the source text they
  match, which the reparse, with only `{` `}` added around a |FunctionDeclaration|, leaves the same and in the
  same order. Residue: the machine's tree walk of the early error rules after a rule
  "must cover" (earlyAt with `tree`) still visits such a node's own children, so in a reparsed cover (`async (a =
  function(){ if (1) function f(){} }) => 0`) the main |IfStatement| rules (IsLabelledFunction of a Statement) are
  not applied to it.
- scope: non-strict code under B.3.3 (the host is a web browser or otherwise supports it).
- decided: coordinator 2026-10-20 (task esl-annexb-b3-rows-b, briefs/handoff-esl-annexb-b3-rows.md; for review)
- covers:
  - reading row-evaluation-if-function
  - reading row-hascallintailposition-if-function
  - reading row-vardeclarednames-if-function
  - reading row-varscopeddeclarations-if-function
  - reading row-containsduplicatelabels-if-function
  - reading row-containsundefinedbreaktarget-if-function
  - reading row-containsundefinedcontinuetarget-if-function
  - reading row-contains-if-function
  - overlay formal-parsenodeswithinprocessed
  - overlay ph-annexb-foreach
  - overlay formal-earlyerrorsof
  - code Ecma.asIfSource
- report: SHORTLIST 19

## agent-events-record-at-creation
- spec: sec-agent-clusters (spec.html 12507)
- quote: Prior to any evaluation of any ECMAScript code by any agent in a cluster, the [[CandidateExecution]] field of
  the Agent Record for all agents in the cluster is set to the initial candidate execution.
- text: The initial candidate execution has an Agent Events Record for each agent of the cluster, set before any agent
  evaluates code; the text does not say how an agent that a host creates while the cluster runs (test262's
  `$262.agent.start`) enters the cluster's candidate execution.
- decision: A new agent's Agent Record shares the surrounding agent's [[CandidateExecution]], and its Agent Events
  Record (empty [[EventList]] and [[AgentSynchronizesWith]]) is appended to [[EventsRecords]] when the agent is
  created (`startBuiltin`), before it evaluates any code. The candidate execution then is the one the text's initial
  one would have become with that agent present from the start and idle until then: its Agent Events Record has no
  events either way, so no read, write or relation differs.
- scope: agents created by the test host's `$262.agent.start`.
- decided: coordinator 2026-10-20 (arc/plans/esl-agents.md D5, task esl-agents-api; for review)
- covers:
  - code Engine.Host.startBuiltin
- report: -

## job-agent-null-realm
- spec: sec-jobs (spec.html 12143); sec-hostenqueuepromisejob (spec.html 12299); sec-hostenqueuegenericjob
  (spec.html 12285)
- quote: If a Realm Record is provided, these operations schedule the job to be performed at some future time in the
  provided realm, in the agent that owns the realm. If *null* is provided instead for the realm, then the job does not
  evaluate ECMAScript code. … It schedules _job_ to be performed at some future time. … in the agent signified by
  _realm_.[[AgentSignifier]]
- text: A job is scheduled in an agent: the agent that owns its realm (the hooks with a realm say "the agent signified
  by _realm_.[[AgentSignifier]]"). HostEnqueuePromiseJob takes a _realm_ that may be *null* (NewPromiseReactionJob
  with an *undefined* handler) and names no agent, so which agent's job loop performs a job of no realm is not said.
- decision: A job of realm *null* belongs to the agent that scheduled it, the surrounding agent of the
  HostEnqueuePromiseJob call; a job with a Realm Record belongs to the agent of its [[AgentSignifier]]. The reading is
  presupposed: the job settles a promise the scheduling agent's reaction holds, and "Jobs must run in the same order
  as the HostEnqueuePromiseJob invocations that scheduled them" orders it among that agent's promise jobs. With one
  agent every reading agrees.
- scope: promise reaction jobs with an *undefined* handler in a test-host agent (`$262.agent.start`).
- decided: coordinator 2026-10-21 (task esl-agents-async, AG4; bus decision 2026-10-21)
- covers:
  - code Ecma.jobAgentOf
- note: tests/run/agent_jobs.js runs a realm-*null* job in an agent (`Promise.resolve().then().then(f)`).
- report: -

## agent-job-base-contexts
- spec: sec-jobs (spec.html 12146-12155)
- quote: when there is no running context in the agent for which the job is scheduled and that agent's execution
  context stack is empty … Perform any host-defined cleanup steps, after which the execution context stack must be
  empty. … The Abstract Closure must return a normal completion, implementing its own handling of errors.
- text: The test host performs an agent's jobs in AgentMain, the code of the agent's first execution context, so the
  agent's stack holds AgentMain's context and its realm's while its jobs run: it is not empty at a job's preparation
  nor after its cleanup. The text does not say how a host's agent other than the one it starts with runs its jobs.
- decision: An agent's job is prepared on AgentMain's two contexts (`prepareJobOn` with base 2) and its cleanup
  leaves those two (`agentCleanupJob`, a stack of length 2). The difference is unobservable: neither context has a
  ScriptOrModule (AgentPrepareJob asserts it), so GetActiveScriptOrModule finds the job's own or none, as on an empty
  stack; a job's preparation pushes the context of its realm, and under a realm-*null* job the running realm is the
  agent's; no job's code reads a context below its own. As main's job loop does, AgentMain asserts that a job returns
  a normal completion: in checked mode, and in every mode at a job erratum's site (`Names.jobErrata`, by
  AgentJobClause). In an unchecked run an abrupt completion with no erratum is ignored, where main's loop ends with it.
- scope: the jobs of agents created by the test host's `$262.agent.start`.
- decided: coordinator 2026-10-21 (task esl-agents-async-d; for review)
- covers:
  - code Engine.Host.prepareJobOn
  - code Engine.Host.agentCleanupJob
  - code Engine.Host.agentMain
- report: -

## tear-free-reads-aligned
- spec: sec-tear-free-aligned-reads 1.a.i (spec.html 53177)
- quote: Assert: The remainder of dividing _readEvent_.[[ByteIndex]] by _readEvent_.[[ElementSize]] is 0.
- text: Tear free reads is a condition on candidate executions, and its step 1.a.i is an Assert inside it: a failing
  Assert is a defect of the text, not an answer, so the step does not say whether an execution with an unaligned
  [[NoTear]] read has tear free reads.
- decision: The memory model's meaning takes the Assert as a conjunct of the condition: an execution with a [[NoTear]]
  read whose [[ByteIndex]] is not a multiple of its [[ElementSize]] does not have tear free reads
  (Ecma.MemoryModel.TearFreeReads). The reading is presupposed: [[NoTear]] read events come from integer TypedArray
  element accesses, whose byte offset and index are multiples of the element size, so no reachable execution tells
  the readings apart. Law L2 (Ecma.Host.MemoryLaws.chooseReadsValid) takes the alignment of the read it appends as its
  premise (Ecma.MemoryModel.NewEvent.IsRead.aligned), and FastHost's proof of L2 takes it from there.
- scope: the memory model; [[NoTear]] reads.
- decided: coordinator 2026-10-21 (review of esl-memory-model-meaning, #11249 note 2; task esl-memory-model-law, AG6;
  for review)
- covers:
  - code Ecma.MemoryModel.TearFreeReads
  - code Ecma.MemoryModel.NewEvent.IsRead.aligned
- note: Hypothesis AlignedNoTearReads, not proved (a whole-run invariant): the shared-read callers
  (GetValueFromBuffer 45796, GetModifySetValueInBuffer 45925, AtomicCompareExchangeInSharedBlock 47523-47525,
  CopyDataBlockBytes 4869 with [[ElementSize]] 1) make [[NoTear]] reads only at a [[ByteIndex]] that is a multiple of
  the [[ElementSize]]. Law L2 (Ecma.Host.MemoryLaws.chooseReadsValid) assumes it of the read it appends
  (Ecma.MemoryModel.NewEvent.IsRead.aligned).
- report: -

# Interpreting phrase meanings

## input-index-of
- spec: sec-regexpbuiltinexec 13.b (spec.html 39825)
- quote: Let _inputIndex_ be the index into _input_ of the character that was obtained from element _lastIndex_ of
  _string_.
- text: In Unicode mode _input_ is a List of code points, and the step does not say which character element _lastIndex_
  of _string_ gives when _lastIndex_ is inside a surrogate pair or at the end of _string_.
- decision: The index of the surrogate pair's character for a _lastIndex_ inside it, and the length of _input_ for
  _lastIndex_ = the length of _string_ (no element there).
- scope: Unicode-mode RegExpBuiltinExec.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse)
- covers:
  - overlay ph-input-index-of
- report: docs/spec-issues/11-regexp-lastindex-inside-surrogate-pair.md, SHORTLIST 10

## split-code-units
- spec: sec-string.prototype.split (spec.html 36562); sec-regexpbuiltinexec (spec.html 39818)
- quote: else let _input_ be a List whose elements are the code units that are the elements of _string_.
- text: "a List consisting of the sequence of code units that are the elements of _head_" goes to
  CreateArrayFromList, whose argument is a List of ECMAScript language values; a code unit is not one.
- decision: At RegExpBuiltinExec's _input_ the phrase is a List of the String's code units, in order. At split, the same
  phrase is the erratum SplitCodeUnitStrings (row split-code-unit-strings).
- scope: RegExpBuiltinExec.
- decided: coordinator 2026-10-13 (merge d161b3751 c3-b14)
- covers:
  - overlay ph-code-units-of-string
- report: SHORTLIST 19

## error-object-terms
- spec: sec-throw-an-exception (spec.html 798); sec-parsetext (spec.html 16433)
- quote: Return ThrowCompletion(a newly created *TypeError* object). … a non-empty List of *SyntaxError* objects
- text: "a newly created *TypeError* object" names no realm and no creation steps; "a *SyntaxError* object" as a type is
  not defined.
- decision: OrdinaryObjectCreate of the current realm's %NativeError.prototype% with an [[ErrorData]] slot holding
  undefined (no *"message"*); as a type, an object with an [[ErrorData]] slot, its prototype untested. An error the text
  creates has no own properties beyond the text's. This is a narrowing of §2's extensions (R10).
- scope: every thrown error the text creates by that phrase; the *SyntaxError* type in signatures.
- decided: coordinator 2026-10-13 (merges d161b3751 c3-b14, 4e74a41a9 types)
- covers:
  - overlay ph-new-error
  - overlay ph-type-syntax-errors
- report: docs/spec-issues/05-parsetext-error-objects.md (related: issues #3868 and #1462, open; neither reports it)

## charset-sort-ties
- spec: sec-compileatom (spec.html 38366); sec-compileatom (spec.html 38454)
- quote: Sort _csSequences_ according to the length of each CharSetElement in descending order.
- text: "Sort _csSequences_ according to the length of each CharSetElement in descending order" leaves the order of
  equal-length elements open.
- decision: Equal lengths keep their order (a stable sort); two equal-length elements that both match leave the same
  MatchState, so the choice is not observable.
- scope: `v`-mode class string disjunctions.
- decided: coordinator 2026-10-13 (merge d161b3751 c3-b14)
- covers:
  - overlay ph-sort-by-length
- report: -

## contains-such-several
- spec: sec-privateelementfind (spec.html 6456); sec-InnerModuleLoading (spec.html 27382);
  sec-FinishLoadingImportedModule (spec.html 29262)
- quote: contains a PrivateElement _entry_ such that _entry_.[[Key]] is _privateName_, then
- text: "If _l_ contains a _T_ _x_ such that _c_, then … _x_" binds _x_ without saying which element when several
  satisfy _c_.
- decision: With none the condition is false; with one, _x_ is it; with several the step stops (no pick).
- scope: such conditions whose consequent reads the bound name.
- decided: coordinator 2026-10-14 (merge 58029fb3c round-j)
- covers:
  - overlay ph-contains-such-binds
- report: -

## delete-derives-error
- spec: sec-delete-operator-static-semantics-early-errors (spec.html 20227)
- quote: ultimately derives a phrase that, if used in place of |UnaryExpression|, would produce a Syntax Error according
  to these rules. This rule is recursively applied.
- text: "ultimately derives a phrase that, if used in place of |UnaryExpression|, would produce a Syntax Error
  according to these rules" names no derivation; a cover derives many phrases.
- decision: The phrase is the |Expression| of the |ParenthesizedExpression| the cover covers, through every nested
  parenthesization ("this rule is recursively applied"); the rules are the clause's two.
- scope: `delete` of a parenthesized operand.
- decided: coordinator 2026-10-17 (merge 0c903ecb8 round-v)
- covers:
  - overlay ph-derives-error
- report: -

## registry-entry
- spec: sec-symbol.for (spec.html 31917); sec-keyforsymbol (spec.html 32158)
- quote: Assert: _globalSymbolRegistry_ does not currently contain an entry for _stringKey_. … Assert:
  _globalSymbolRegistry_ does not currently contain an entry for _symbol_.
- text: "does not currently contain an entry for _x_" is not defined for the GlobalSymbolRegistry List.
- decision: An entry for a String is a Record whose [[Key]] is it; for a Symbol, one whose [[Symbol]] is it.
- scope: those Asserts.
- decided: coordinator 2026-10-13 (merge d161b3751 c3-b14)
- covers:
  - overlay ph-no-registry-entry
- report: SHORTLIST 19

## has-attribute-values
- spec: sec-candeclareglobalfunction (spec.html 11358)
- quote: _existingProperty_ has attribute values { [[Writable]]: *true*, [[Enumerable]]: *true* }
- text: "has attribute values { [[Writable]]: *true*, [[Enumerable]]: *true* }" is not defined.
- decision: Every attribute the Record lists is a field of the descriptor with the same value (SameValue); attributes
  it does not list are not tested.
- scope: CanDeclareGlobalFunction.
- decided: coordinator 2026-10-13 (merge d161b3751 c3-b14)
- covers:
  - overlay ph-has-attribute-values
- report: SHORTLIST 19

## tobigint-boolean-literals
- spec: sec-tobigint (spec.html 5258-5264)
- quote: Return `1n` if _primitive_ is *true* and `0n` if _primitive_ is *false*.
- text: The Boolean row writes its results as source-text literals and its two cases as one sentence.
- decision: The phrase "_a_ if _c_ and _b_ if _d_" reads the two cases.
- scope: ToBigInt.
- decided: coordinator 2026-10-14 (merge c8e662201 docs-arc)
- covers:
  - overlay ph-if-and-if
- report: docs/spec-issues/28-tobigint-boolean-literals.md

## annexb-replacing-early-errors
- spec: sec-functiondeclarationinstantiation 32.a.i.2 (spec.html 14018); sec-globaldeclarationinstantiation 12.b.ii.2
  (spec.html 26533); sec-evaldeclarationinstantiation 13.b.ii (spec.html 30285)
- quote: If replacing the |FunctionDeclaration| _funcDecl_ with a |VariableStatement| that has _funcName_ as a
  |BindingIdentifier| would not produce any Early Errors for _func_
- text: The condition names a source transformation, not an operation, and "Early Errors for _func_" applies early
  error rules to a function object, not a Parse Node.
- decision: The source text of the parse that made _funcDecl_ (through every cover), with _funcDecl_'s replaced by
  `var` _funcName_ `;`, parsed again with the same goal symbol and context; the condition holds when that parse
  succeeds and EarlyErrorsOf finds none in it. Early Errors for _func_ reads as _func_'s [[ECMAScriptCode]] with its
  [[FormalParameters]], the code of the function; the parse outside _body_, _script_ or that code is unchanged and
  had no early errors, so checking the whole parse is checking that code.
- scope: Annex B.3.2's block-level function declarations in function, global and eval code.
- decided: coordinator 2026-10-20 (decision log; brief handoff-t262-stop-evaldecl option (a), task t262-annexb-replacing)
- covers:
  - overlay ph-annexb-replacing
  - overlay prim-replacedsourcetext
- report: SHORTLIST 19

## annexb-evaluated-in-place
- spec: sec-functiondeclarationinstantiation 32.a.i.2.c (spec.html 14024); sec-globaldeclarationinstantiation
  12.b.ii.2.a.ii.3 (spec.html 26541); sec-evaldeclarationinstantiation 13.b.ii.7.b (spec.html 30314);
  sec-function-definitions-runtime-semantics-evaluation 1 (spec.html 24012-24016)
- quote: When the |FunctionDeclaration| _funcDecl_ is evaluated, perform the following steps in place of the
  |FunctionDeclaration| Evaluation algorithm provided in
- text: The step registers steps to run later, at another algorithm's evaluation of _funcDecl_, with no operation that
  does so: it does not say from when or for how long they replace FunctionDeclaration Evaluation, which variables they
  read, or what that Evaluation returns.
- decision: The nested steps are an Abstract Closure with no parameters capturing the earlier variables they read
  (_funcName_), stored for _funcDecl_ by SetEvaluationSteps, a later such step for the same Parse Node replacing it.
  FunctionDeclaration Evaluation first asks EvaluationStepsOf(this Parse Node) and, when there are steps, calls them
  and returns their abrupt completion if they give one (as SortIndexedProperties' reading calls _sortCompare_); then
  its own step returns ~empty~. The steps return ~unused~ (spec.html 14029, 26893, 30635), which is
  not a completion value (UpdateEmpty, spec.html 4099, would keep it, and PerformEval, spec.html 30161, maps only
  ~empty~ to *undefined*), so the Evaluation they replace keeps its ~empty~.
- scope: Annex B.3.2's block-level function declarations in function, global and eval code.
- decided: coordinator 2026-10-20 (task t262-annexb-evaluated, goal 6, user #16112; draft for the coordinator's review)
- covers:
  - overlay ph-annexb-evaluated
  - overlay prim-setevaluationsteps
  - overlay prim-evaluationstepsof
  - code Ecma.Prims.Context.setEvaluationSteps
  - code Ecma.Prims.Context.evaluationStepsOf
  - code Ecma.State.evalSteps
- report: SHORTLIST 19

# Sort doubts

## time-value-range
- spec: sec-time-values-and-time-range (spec.html 33764-33775); sec-epoch-nanoseconds (spec.html 34042-34048)
- quote: A time value supports a slightly smaller range of -8,640,000,000,000,000 to 8,640,000,000,000,000 milliseconds.
  … It supports the same range as a time value but expressed in nanoseconds
- text: "time value" is defined without a range, the paragraph gives ±8.64 × 10^15; "epoch nanoseconds count"
  includes its range.
- decision: The time value sort has no range; the epoch nanoseconds count sort keeps its range.
- scope: Date.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt time value
  - doubt epoch nanoseconds count
- report: SHORTLIST 16

## undefined-object-terms
- spec: sec-ordinary-object-internal-methods-and-internal-slots (spec.html 12731-13296); sec-array-exotic-objects
  (spec.html 14310-14452); sec-built-in-function-objects (spec.html 14051-14177)
- quote: A built-in function object is an ordinary object; it must satisfy the requirements for ordinary objects
- text: "extensible" has no dfn; exotic objects' "other essential internal methods use the definitions in 10.1";
  "built-in" is about provenance, which state cannot decide.
- decision: Tests by observation: [[Extensible]]; the method identity; an ordinary object whose [[Call]] is 10.3.1's.
- scope: sort tests.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt extensible
  - doubt Array / String / arguments exotic object, TypedArray, module namespace exotic object
  - doubt built-in
- report: -

## data-block-shared
- spec: sec-data-blocks (spec.html 4477-4563)
- quote: The Data Block specification type is used to describe a distinct and mutable sequence of byte-sized (8 bit)
  numeric values.
- text: A Shared Data Block is called "a data block", yet headers say "a Data Block or a Shared Data Block".
- decision: The two are disjoint (IsDataBlock, IsSharedDataBlock).
- scope: buffers.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt Data Block / Shared Data Block
- report: SHORTLIST 19

## binding-terms
- spec: sec-environment-records (spec.html 10224-11627)
- quote: Environment Record is a specification type used to define the association of |Identifier|s to specific
  variables and functions
- text: "binding" has no dfn and no value; "strict", "mutable", "uninitialized" bindings neither.
- decision: Residue; the env.emu readings give bindings their fields.
- scope: Environment Records.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt binding, strict, mutable, uninitialized
- report: -

## undefined-instance-terms
- spec: sec-properties-of-regexp-instances (spec.html 40036-40048); sec-properties-of-array-iterator-instances
  (spec.html 41792-41843)
- quote: RegExp instances have internal slots [[OriginalSource]], [[OriginalFlags]], [[RegExpRecord]], and
  [[RegExpMatcher]].
- text: "an initialized RegExp instance" and the iterator "Instance" phrases are not defined terms.
- decision: A RegExp instance whose [[RegExpMatcher]] is set; the iterator phrases read as "has the slots of".
- scope: sort tests.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt initialized RegExp instance
  - doubt Array Iterator Instance, RegExp String Iterator Object Instance, For-In Iterator instance
- report: SHORTLIST 19

## pattern-terms
- spec: sec-pattern-notation (spec.html 37797-37875); sec-runtime-semantics-unicodematchproperty-p (spec.html
  39324-39353)
- quote: is a Unicode property name listed in the “Property name” column of
- text: "single" has no dfn; "Unicode property name / value" are emu-not-ref and never defined.
- decision: "single" is one character; property names and values come from the spec tables and the pinned UCD files.
- scope: RegExp.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt single
  - doubt Unicode property name / Unicode property value
- report: -

## record-kind-terms
- spec: sec-private-names (spec.html 4706-4709); sec-synthetic-module-records (spec.html 28979-29175)
- quote: The Private Name specification type is used to describe a globally unique value … A Synthetic Module Record is
  used to represent information about a module that is defined by specifications.
- text: Private Name's [[Description]] is called an internal slot; Synthetic Module Record is a Module Record
  subclass only by implication.
- decision: [[Description]] is a field; Synthetic Module Record has super Module Record.
- scope: sort tests.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt Private Name
  - doubt Synthetic Module Record
- report: SHORTLIST 17a

## code-point-and-sign-terms
- spec: sec-source-text (spec.html 16311-16451); sec-mathematical-operations (spec.html 886-920)
- quote: ECMAScript source text is a sequence of Unicode code points.
- text: "sequence of Unicode code points" is never defined; "non-negative" and "positive" have no definition.
- decision: A List of code points (any "sequence of" values is a List of them in order; a CharSetElement that is not a
  List is a sequence of one character); ≥ 0 and > 0 on mathematical values, with +0 positive and -0 negative for
  Numbers.
- scope: sort tests.
- decided: coordinator 2026-10-13 (merge 206b12c9a esl-sorts)
- covers:
  - doubt sequence of Unicode code points
  - doubt non-negative / positive
  - overlay ph-type-sequence-of
  - overlay ph-code-point-sequence
  - overlay ph-charset-element-longer-than-one
- report: SHORTLIST 19

## code-literal-code-points
- spec: sec-multiplicative-operators-runtime-semantics-evaluation 1 (spec.html 20422);
  sec-applystringornumericbinaryoperator 6.b (spec.html 21000-21024)
- quote: Let _opText_ be the source text matched by |MultiplicativeOperator|.
- text: _opText_ is "the source text matched by |MultiplicativeOperator|", a sequence of code points, yet the
  parameter's type and step 6's `is` comparisons give it as a code literal (`/`, `%`); the spec never says what
  a code literal is as a value.
- decision: A code literal is a String; `v is w` with w a String reads a List of code points v as the String of
  them (`isVals`, lean/Ecma/Ops/Leaf.lean), as a table's code cells are read (`codeKey`).
- scope: every `is` comparison of a List with a String; in practice BigInt `/` and `%`.
- decided: coordinator 2026-10-17 (brief briefs/fixup/esl-bigint-optext.md)
- covers:
  - doubt sequence of Unicode code points
- report: -

# Model choices

## promise-job-null-realm-code
- spec: sec-hostenqueuepromisejob (spec.html 12310)
- quote: When the _realm_ is *null*, no user ECMAScript code will be evaluated and no new ECMAScript objects
- text: HostEnqueuePromiseJob's note says "When the _realm_ is *null*, no user ECMAScript code will be evaluated and no
  new ECMAScript objects (e.g. Error objects) will be created". NewPromiseReactionJob with an undefined handler still
  calls the derived promise's resolving functions, which are user code when a species constructor supplies them.
- decision: Literal, with no stop, because a note states no requirement: an editorial report, not an erratum
  (nothing in the model reads the note). Such a job runs with no execution context
  pushed (prepareJob). The proposed reading changes the note.
- scope: promise jobs of revoked-proxy or cross-realm handlers.
- decided: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse); user 2026-10-18 (U2)
  user 2026-11-18 (F2, the errata review: a report, not an erratum)
- covers:
  - file docs/spec-issues/47-promise-job-null-realm-code.md
- report: docs/spec-issues/47-promise-job-null-realm-code.md

## ordinaryset-receiver-has-property
- spec: sec-ordinarysetwithowndescriptor 2.d.i (spec.html 13132)
- quote: Assert: _receiver_ does not currently have a property _propertyKey_.
- text: The Assert "_receiver_ does not currently have a property _propertyKey_" rests on the receiver's
  [[GetOwnProperty]] answer one step before. A Proxy receiver's trap may answer *undefined* for a configurable
  property of its extensible target: read on the receiver's own storage the Assert is vacuous for every Proxy, read
  through the Proxy it fails.
- decision: Literal. The Assert has no checkable meaning (assert-provenance, permanent-sentences.txt), so a run passes it
  unchecked and does not stop under any reading: an editorial report, not an erratum. No reading looks through
  the Proxy.
- scope: [[Set]] with a Proxy receiver whose getOwnPropertyDescriptor trap hides a target property.
- decided: user 2026-10-18 (#7958: 'register the 2 unregistered ones'); coordinator 2026-10-18 (#8200: no meaning
  change)
  user 2026-11-18 (F2, the errata review: a report, not an erratum)
- covers:
  - file docs/spec-issues/38-ordinaryset-receiver-has-property.md
- note: The witness tests/run/ordinaryset_proxy_receiver.js returns *true* and sets the target's property with no
  stop on the machine, which reports the step as passed unchecked.
- report: docs/spec-issues/38-ordinaryset-receiver-has-property.md

## unicode-version
- spec: sec-string.prototype.normalize 7 (spec.html 36229)
- quote: as specified in the latest Unicode Standard, Normalization Forms.
- text: "the latest Unicode Standard" is an undated normative reference: the results change with Unicode releases.
- decision: The model's Unicode data is the UCD release the pinned test262 expects (17.0.0, flake.nix's `ucd`),
  through UnicodeLaws.
- scope: normalization, case mapping, property escapes, identifiers.
- decided: user 2026-10-18 (#9410, U3)
- covers:
  - code Ecma.Model.UnicodeLaws
- report: -

## sab-single-agent-reads
- spec: sec-getrawbytesfromsharedblock 6 (spec.html 45491); sec-getmodifysetvalueinbuffer 9.c (spec.html 45620);
  sec-atomiccompareexchangeinsharedblock 4 (spec.html 47216); sec-copydatablockbytes 6.a.iv (spec.html 4545)
- quote: whose elements are nondeterministically chosen byte values … a nondeterministically chosen byte value
- text: A read of a Shared Data Block takes "nondeterministically chosen byte values", constrained only by the memory
  model's valid-execution conditions. With one agent those conditions leave one value, the last write's bytes, so the
  readings restate the text there; the decision is the scope.
- decision: With one Agent Events Record the four reads take the last write's bytes, the value the memory model
  forces. With several, the read is a scheduling point outside a critical section (AgentInterleave, where
  EnteredCriticalSections() is empty), then takes ChooseSharedBytes' bytes (overlay formal-choosesharedbytes): the
  host chooses the write event each byte reads from (ChooseReadsBytesFrom, row choose-reads-bytes-from), and the
  bytes are composed from those events as ComposeWriteEventBytes composes them, a ReadModifyWriteSharedMemory event's
  from its [[ChosenValue]] (valid chosen reads, spec.html 53136-53148).
- scope: every cluster; Host.WF holds each host to law L1 (an event per byte, from the execution, writing that byte)
  and law L2 (chooseReadsValid: a valid execution whose memory order is the interleaving order stays valid with the
  read appended, reading the chosen events).
- decided: user 2026-10-16 20:52 (briefs/handoff-coordinator.md: 'Yes, single-agent readings'); the stop: user
  2026-10-20 (#9576, model-audit R11 option (a)); several agents: coordinator 2026-10-20 (arc/plans/esl-agents.md
  D-3, task esl-agents-reads; for review)
- covers:
  - reading definition-sec-getrawbytesfromsharedblock-6
  - reading definition-sec-getmodifysetvalueinbuffer-9.c
  - reading definition-sec-atomiccompareexchangeinsharedblock-4
  - reading definition-sec-copydatablockbytes-6.a.iv
  - overlay formal-choosesharedbytes
  - code Ecma.Host.MemoryLaws.chooseReadsValid
- note: With one Agent Events Record, every valid extension's chosen value is SingleAgentReadBytes' bytes,
  through agent order alone: no use of
  happens-before's ~init~ rule (row init-happens-before-overlap).
- report: -

## annexb-module-reparse
- spec: sec-html-like-comments (spec.html 53808); sec-forbidden-extensions (spec.html 30005); sec-syntactic-grammar
  (spec.html 404)
- quote: this extension is not allowed when parsing source text using the goal symbol |Module| … The sequence of tokens
  originally matched by _p_ is parsed again using _n_ as the goal symbol.
- text: B.1.1 is "not allowed when parsing source text using the goal symbol |Module|", and a parse within a Module may
  have another goal: §5.1.5's cover and early-error reparses parse "the sequence of tokens originally matched", so the
  text's results are definite. The model reparses a node's source text, not tokens, which with B.1.1 on could read
  `<!--` as a comment where the Module's tokens were `<` `!` `--`.
- decision: The model reparses a node's source text. The invocation's ParseCx.module (set when the goal is |Module|,
  inherited by a reparse of a node that invocation made: moduleParses, as strictParses) makes that reparse read B.1.1 as
  a reparse of the Module's tokens would: the grammar context's Ctx.module is it, so B.1.1's overlay is off there. Eval
  code and dynamic function text parse as Scripts.
- scope: Annex B hosts; the lexical grammar of a Module and of the reparses within one.
- decided: coordinator 2026-10-18 (arc/plans/esl-annexb-parse.md M1, decision log; task esl-annexb-meaning-ctx)
- covers:
  - file docs/spec-issues/42-annexb-module-goal-reparse.md
- report: docs/spec-issues/42-annexb-module-goal-reparse.md (becomes a SHORTLIST 19 line)

## escape-pattern-same-invocation
- spec: sec-escaperegexppattern 5 (spec.html 39617-39641)
- quote: that behaves identically to the constructed regular expression
- text: "_escapedPattern_ may or may not differ from _pattern_; however, the Abstract Closure that would result from
  evaluating _escapedPattern_ as a _patternSymbol_ must behave identically to the Abstract Closure given by the
  constructed object's [[RegExpMatcher]] internal slot" does not say in which parser invocation _escapedPattern_ is
  parsed. In the model a Parse Node carries its invocation, so the separate-invocation reading is unsatisfiable: an
  escaped String's source text differs from _pattern_'s, and a program's CompilePattern can read the invocation.
- decision: EscapePattern's String is compared as a |Pattern| parsed in _pattern_'s own invocation
  (`Host.WFIn.escapeBehaviour`). This is strictly weaker than the separate-invocation law, and the spec's CompilePattern
  reads no invocation. Hosts that answer _pattern_ itself meet it at every program.
- scope: EscapePattern's behaviour law (`Host.WFIn`), every host.
- decided: user 2026-10-18 (#8761, option A1 of #8484); the premise `st < s.parses`: user 2026-10-24 (#24007, U1 a)
- covers:
  - overlay prim-escapepattern
- note: The stamp-reading node primitives are InParseJSONScript, StrictFromOutside, InDirectEval and GoalSymbolOf (the
  state's jsonParses, strictParses, directParses, roots and covers). `Host.WFIn.escapeBehaviour` parses both at the same
  stamp and runs CompilePattern's closures from one state past that invocation (`st < s.parses`, which every `Issued`
  state with the root recorded meets: `escape_premise_fastP`) that holds nothing else of it (`StampFree`), each
  tree recorded as the invocation's root (`State.addRoot`); the law is asked at the spec's program. Over every program it holds only for the answer _pattern_ itself (nodeSource); over every state it
  fails even at the spec's program (sameNode shares a stale root or memo entry).
- report: -

## unchecked-asserts
- spec: sec-algorithm-conventions (spec.html 708)
- quote: A step that begins with “Assert:” asserts an invariant condition of its algorithm.
- text: An Assert "asserts an invariant"; a prose Assert with no declared meaning cannot be checked.
- decision: An Assert with no declared meaning is never checked, in any mode. permanent-sentences.txt lists those unchecked on
  purpose (future and provenance Asserts); asserts-open.txt lists the 6 that have no meaning yet.
- scope: every run.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent Cond.unchecked
  - file spec/formal/permanent-sentences.txt
  - file spec/formal/asserts-open.txt
- report: -

## canonical-carriers
- spec: sec-samevaluenonnumber 3 (spec.html 5745)
- quote: If _x_ and _y_ have the same length and the same code units in the same positions, return *true*.
- text: The text's equality of values is by content (Strings by their code units, Lists by their elements), and the
  model's carriers are abstract.
- decision: Lean `=` on a carrier is the text's equality (the laws eq_iff, str_ext, strEq_iff, seq_ext, symEq_iff,
  addrEq_iff and nodeEq_iff), so a model's carriers are canonical: a rope String, an unnormalized rational or a Seq with
  spare capacity is not a model. Fast (`Array`) and Ref (`List`) both meet it.
- scope: every model (Ecma.Model.Laws).
- decided: coordinator 2026-10-18 (readings audit #9128 §8; model-audit M4)
- covers:
  - code Ecma.Model.Laws.eq_iff
  - code Ecma.Model.Laws.strEq_iff
  - code Ecma.Model.Laws.seq_ext
- report: -

## annexb-block-function-search-root
- spec: sec-functiondeclarationinstantiation (spec.html 14016); sec-globaldeclarationinstantiation (spec.html 26531);
  sec-evaldeclarationinstantiation (spec.html 30283)
- quote: such that … Contains _x_ is *true*
- text: B.3.2's three block-function steps take "any |Block|, |CaseClause|, or |DefaultClause| _x_ such that _P_
  Contains _x_ is *true*" (_P_ is _code_, _script_ or _body_). Contains walks only _P_'s own tree, so every _x_ the
  test admits is a node of that tree: searching the other trees made so far adds nothing.
- decision: The step's phrase (ph-annexb-foreach) iterates ParseNodesWithin(_P_) in pre-order and keeps the Contains
  test, which drops nodes inside nested functions, classes' bodies and arrow functions. No primitive enumerates every
  parse tree. The machine reads only _P_'s tree, so it is preserved by State.Obs, which relates states only up to
  their live roots (World.keepRoots: dead and garbage stamps' records are ignored); a search over every recorded root
  would differ on related states.
- scope: the three web-compat steps (the host is a web browser: --web-browser).
- decided: coordinator 2026-10-19 (bus #12988, task esl-annexb-b322-fix)
- covers:
  - overlay ph-annexb-foreach
  - overlay formal-parsenodeswithin
  - code Ecma.Prims.Nodes.instanceOf
- report: -

## annexb-block-function-arguments
- spec: sec-functiondeclarationinstantiation 22.f (spec.html 13978); sec-functiondeclarationinstantiation 32.a.i.2
  (spec.html 14018); sec-functiondeclarationinstantiation 32.a.i.2.b (spec.html 14020)
- quote: Let _paramBindings_ be the list-concatenation of _paramNames_ … _paramNames_ does not contain _funcName_ …
  _funcName_ is not *"arguments"*
- text: B.3.2.1's test is "_paramNames_ does not contain _funcName_", not _paramBindings_ (which adds "arguments" when
  an arguments object is made), so a block-level `function arguments() {}` in non-strict function code is hoisted:
  its evaluation sets the var-scoped "arguments" binding, replacing the arguments object. The text is definite, and
  upstream chose it (ecma262 #891, closing #815, kept _parameterNames_ here and added the `is not "arguments"` guard;
  #889's engine survey). test262's annexB/language/function-code/block-decl-func-skip-arguments.js expects the
  arguments object to stay: it was written to the text before #891 (its info quotes "Append "arguments" to
  parameterNames") and is stale (test262 #5113, PR #5112); staging/sm/lexical-environment/
  block-scoped-functions-annex-b-arguments.js expects the function.
- decision: The literal text: _paramNames_, no erratum. block-decl-func-skip-arguments.js is a known fail on every
  mode, not a finding: stage suite excludes it (tests/test262/suite.conf). The staging/sm test is a `pass`
  row of tests/test262/regress.txt, on the web-browser host.
- scope: Annex B.3.2.1, a block-level FunctionDeclaration named `arguments` in non-strict function code (the host is
  a web browser: --web-browser).
- decided: user 2026-10-21 (#17616, option a of #17216; decision log 298)
- covers:
  - overlay ph-annexb-replacing
- note: On 2026-10-21 the model fails block-decl-func-skip-arguments.js (a Test262Error: `arguments` is
  the function after the block) and pass the staging/sm test.
- report: -

# Host-choice defaults of the test hosts

## annexb-feature-choices
- spec: sec-additional-ecmascript-features-for-web-browsers (spec.html 53795-53797);
  sec-functiondeclarations-in-ifstatement-statement-clauses (spec.html 54599)
- quote: The content of this annex is normative but optional if the ECMAScript host is not a web browser. … where the
  feature involves particular wording in an algorithm or early error rule, this is guarded by the condition that …
  the relevant feature. Web browsers are required to support all such features. … The semantics of such a synthetic
  |BlockStatement| includes the web legacy compatibility semantics
- text: Each Annex B feature is guarded on its own ("the host is a web browser or otherwise supports" its clause), so
  a host that is not a web browser may support some features and not others: B.3.3 without B.3.2, for one.
- decision: Each feature is its own host choice, keyed by its clause: WebBrowser with `[.choice 0, .clause c]`
  ("the host is a web browser or otherwise supports c"), asked at the gated steps and early-error spans (B.3.1,
  B.3.2, B.3.4, B.3.6, B.3.9) and by the parser for each grammar overlay (B.1.1, B.1.2, B.3.3, B.3.5);
  `[.choice 1, .absent]` asks "the host is a web browser". Laws: an answer is fixed for a run, and every feature's
  answer is true where the host is a web browser. No law ties two features: on a host with B.3.3 and without B.3.2,
  B.3.3's synthetic Block is an ordinary Block, B.3.2's steps reading B.3.2's own answer.
- scope: Annex B's grammar overlays, gated steps and early-error spans; not B.2's properties
  (normative-optional-properties) or the host hooks of B.3.7 and B.3.8.
- decided: user 2026-10-18 (#9410, U3); B.3.3 without B.3.2: coordinator 2026-10-13 (merge 8ce3e1026 esl-parse),
  user 2026-10-18 (U2)
- covers:
  - host WebBrowser
  - code Ecma.Host.OptionalLaws.webBrowser
  - code Ecma.Host.OptionalLaws.webBrowserSupports
  - code Grammar.AnnexB.Set
  - code Engine.Host.annexBClauses
  - code Engine.Host.HostOpts.annexB
- note: the test hosts take a feature from `--annex-b <sec-id>` (ecma-run); tests/run/catch_var_annexb.js,
  annexb_if_function_without_b32.js and the annexb_*_host.js / annexb_*_absent.js pairs.
- report: -

## iso-year-form
- spec: sec-date.prototype.toisostring 7 (spec.html 35404); sec-date-time-string-format (spec.html 34450)
- quote: four decimal digits from 0000 to 9999, or as an expanded year
- text: `YYYY` admits a year in 0..9999 as four digits or as an expanded year, and toISOString does not say which.
- decision: The host's (ExpandedYearForm, a logged choice), asked only for a year in 0..9999; any other year is
  expanded. Every host's answer obeys Host.WF.expandedYearForm: a Boolean (or a stop), the state unchanged. The default
  hosts answer four digits, as test262 asks.
- scope: Date.prototype.toISOString on the default test hosts.
- decided: user 2026-10-18 (#9410, U3)
- covers:
  - reading definition-sec-date.prototype.toisostring-7
  - host ExpandedYearForm
- note: test262 requires four digits in 0..9999 (built-ins/Date/15.9.1.15-1.js,
  built-ins/Date/prototype/toISOString/15.9.5.43-0-4.js) and an expanded year elsewhere
  (built-ins/Date/parse/time-value-maximum-range.js).
- report: -

## annex-b-web-browser
- spec: sec-additional-ecmascript-features-for-web-browsers (spec.html 53793-54714); sec-web-scripting
  (spec.html 285-290)
- quote: The ECMAScript language syntax and semantics defined in this annex are required when the ECMAScript host is a
  web browser. The content of this annex is normative but optional if the ECMAScript host is not a web browser.
- text: Annex B is normative-optional, required of web browsers; whether a host is one, and which features a host
  that is not one otherwise supports, are the host's (annexb-feature-choices).
- decision: The default hosts (FastHost, RefHost) are not web browsers and otherwise support no Annex B feature:
  every step, early-error span and grammar overlay guarded by "the host is a web browser or otherwise supports …"
  takes the unsupported branch. `--web-browser` makes the test host a web browser (every feature supported) and
  `--annex-b <sec-id>` supports one feature. The normative optional built-in properties are still provided
  (normative-optional-properties): the default hosts support those, not Annex B's syntax and steps. Every host's
  answer obeys Host.WF.webBrowser: a Boolean (or a stop), the state unchanged, one Boolean for the same arguments in
  every state; which Boolean stays the host's. A host whose WebBrowser answers are false uses the default job
  callbacks (job-callback-hooks).
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults; merge 592431020 b1-s0b-fastp); user 2026-10-18
  (#9410, U3)
- covers:
  - silent EarlySentence.den
  - silent choice (WebBrowser)
  - host WebBrowser
- report: -

## normative-optional-properties
- spec: sec-conformance (spec.html 239); sec-sharedarraybuffer-constructor (spec.html 45984)
- quote: A conforming implementation of ECMAScript may choose to implement or not implement Normative Optional
  subclauses … it may omit the *"SharedArrayBuffer"* property of the global object.
- text: A conforming implementation may implement Normative Optional subclauses or not, and a host without concurrent
  access to SharedArrayBuffers may omit the global's *"SharedArrayBuffer"* property.
- decision: The default hosts provide every normative optional built-in property (HostSupportsOptional true; the
  realm's PropertyProvided) and keep *"SharedArrayBuffer"* (OmitSharedArrayBuffer false).
- scope: the default test hosts' realms.
- decided: coordinator 2026-10-15 (merge 05925872f round-p)
- covers:
  - host HostSupportsOptional
  - host OmitSharedArrayBuffer
- report: -

## property-order
- spec: sec-setdefaultglobalbindings 2 (spec.html 11873); sec-createintrinsics (spec.html 11847-11861)
- quote: For each property of the Global Object specified in clause
- text: The order in which a realm's built-in properties are created is not fixed ("For each property of the Global
  Object"; CreateIntrinsics), and Object.getOwnPropertyNames observes it.
- decision: The host's (PropertyOrder); the default hosts create them in document order, the order of their
  definitions in spec.html.
- scope: the default test hosts' realms.
- decided: coordinator 2026-10-15 (merge 05925872f round-p)
- covers:
  - host PropertyOrder
- report: -

## forin-default-order
- spec: sec-enumerate-object-properties (spec.html 22771-22817)
- quote: The mechanics and order of enumerating the properties is not specified
- text: EnumerateObjectProperties's iterator is implementation-defined within its prose rules.
- decision: The default hosts' ForInStep follows CreateForInIterator's actions (sec-createforiniterator) while every
  action so far was its, else asks [[OwnPropertyKeys]] of the object (forInChoice).
- scope: the default test hosts' for-in.
- decided: coordinator 2026-10-15 (merge 07ce0fb07 round-l)
- covers:
  - host ForInStep
- report: -

## date-parse-fallback
- spec: sec-date.parse (spec.html 34791-34807); sec-date-time-string-format (spec.html 34439-34561); sec-expanded-years
  (spec.html 34563-34565)
- quote: any implementation-specific heuristics or implementation-specific date formats
- text: A String not in the Date Time String Format may fall back to "any implementation-specific heuristics or
  implementation-specific date formats"; the round trips of toString, toUTCString and toISOString are a "should".
- decision: Host.WF states every fixed part as a law of ParseDateString (HostLaws.lean): a time value, *NaN* or an
  integral Number within ±8.64 × 10^15, never -0𝔽 (parseDateString); a valid instance of the format by its fields
  and substitutes, date-only and offset forms as UTC less the offset (dateFormUTC), date-time forms without an offset
  as UTC of a local time (dateFormLocal), out-of-bounds element values and -000000 as *NaN* (dateFormIllegal);
  toISOString's String gives any time value (isoRoundTrip, from dateFormUTC). The round trips of toUTCString and
  toString are a "should" (spec.html 34795-34800), so a host feature, `Should.dateRoundTrip` (the host's `does`,
  fixed for the run): where it is true, for a time value with milliseconds 0, the Strings of toUTCString
  (utcStringRoundTrip) and of toString (DateString, TimeString, TimeZoneString; toStringRoundTrip) give it; where it
  is false, those Strings are as loose as other Strings. Both default hosts set it (their choice). Loose: other
  Strings (an integral in-range value or *NaN*), a day in (DaysInMonth, 31], `24` with nonzero `mm`, `ss` or `sss`,
  an offset `HH` of 24, and toString's String where the offset is not whole minutes under a day. Both default
  hosts' ParseDateString read with one parser over code units (`dateParse`, lean/Ecma/Host/DateParse.lean): the format (a local time as UTC; neither host has local
  time zone rules, so dateFormLocal is vacuous on both), toUTCString's and toString's forms with any offset and time
  zone name, else *NaN*. RefHost answers its value as a rational Number; FastHost as `numOf` of it where that reads
  back as it (`parseDateNum`; a binary64 holds every in-range integer, so this holds, but it is checked, not
  proved, and a failed check stops as residue). Date.parse is ToString of its argument, then ParseDateString
  (formal-date.parse), as the Date constructor's step 4.c.ii.2.
- scope: Date.parse and the Date constructor; the laws on every host, the readings on the default test hosts.
- decided: coordinator 2026-10-14 (merge cfe4a589d round-h); formal-date.parse coordinator 2026-10-17
  (briefs/fixup/esl-builtin-prose.md); the laws user 2026-10-17 (#7168); FastHost's answer by the shared parser
  user 2026-10-18 (#7168 a); the round trips a host feature user 2026-10-18 (#9576)
- covers:
  - host ParseDateString
  - overlay formal-date.parse
- report: -

## native-function-source
- spec: sec-function.prototype.tostring (spec.html 31662-31682)
- quote: The representation must have the syntax of a |NativeFunction|.
- text: A built-in's source text is implementation-defined, constrained only to the |NativeFunction| syntax.
- decision: The law asks for `function ` N `() { [native code] }` with N a name of the described form (empty, or
  `get `/`set ` or nothing, then an ASCII IdentifierName or `[Symbol.` one `]`), N = [[InitialName]] where that is a
  matched or empty String; that each such String has the NativeFunction syntax with N as its portion is stated over
  the grammar (NativeFormParses), not assumed. RefHost and FastHost answer N = [[InitialName]] where the form admits
  it, the empty N where [[InitialName]] is not a String, else residue; neither parses at run time.
- scope: Function.prototype.toString of built-ins on the default test hosts.
- decided: coordinator 2026-10-14 (merge cfe4a589d round-h); the form: user 2026-10-24, coordinator (bus #25913)
- covers:
  - host NativeFunctionSource
- report: -

## native-function-source-form
- spec: sec-function.prototype.tostring 3 (spec.html 31669)
- quote: The representation must have the syntax of a |NativeFunction|.
- text: Any String with the NativeFunction syntax conforms, white space, line terminators and comments between its
  tokens and non-ASCII or escaped names among them. NativeFunctionSource's law admits a narrower form.
- decision: A model choice, not a reading of the text: the host laws' NativeFunctionSource law admits only `function ` N
  `() { [native code] }`, N empty or, after `get `, `set ` or nothing, an ASCII IdentifierName without escapes or
  `[Symbol.` one `]`. A host answering another conforming String is not WF, and an [[InitialName]] matched by
  NativeFunctionAccessor? PropertyName that is not such an N has no answer the law admits (residue). Conformance does
  not need the narrowing; it is kept for proof cost. The steps run as written.
- scope: Function.prototype.toString of built-ins and of callable objects without source text, on every host
  Host.WF admits.
- decided: user 2026-10-24 (the form); the form as the law, recorded as an erratum of the implementation: user
  (#26410, decision_log 427)
  user 2026-11-18 (F2, the errata review: a decisions row, not an erratum)
- covers:
  - code Ecma.nativeName
  - overlay prim-nativefunctionsource
- report: docs/spec-issues/14-nativefunction-initialname.md (header only; not part of the report)

## escape-pattern
- spec: sec-escaperegexppattern 4-5 (spec.html 39617-39641); sec-updatemodifiers (spec.html 38586);
  sec-regexpinitialize 19 (spec.html 39167); sec-regexpbuiltinexec 11 (spec.html 39818)
- quote: Let _escapedPattern_ be a String in the form of a _patternSymbol_ equivalent to _pattern_
- text: The escaped pattern is "a String in the form of a |Pattern|" with the step's escapes, otherwise open.
- decision: RefHost: *"(?:)"* for the empty pattern, else the minimal escape of `/` and line terminators; FastHost:
  the pattern itself where it needs no escape (non-empty, no unescaped `/`, no line terminator) and *"/"*, it, *"/"*
  and the flags parse as a |RegularExpressionLiteral| whose body it is; else RefHost's answer where that is such a
  body and a runtime check finds its |Pattern| (the flags' parameters) in every grammar context, strict or not,
  under both grammar readings (`patternAt`), for the empty pattern also each |Pattern| tree of it and of
  *"(?:)"* the one `empty_sim` takes (`emptyShapes`); else it stops (residue). The check proves FastHost's
  `Host.WF` unconditionally. At the spec's program the behaviour law holds for the empty pattern
  (`escapeSim_spec`, by `empty_sim`), and for the others under the named hypothesis `EscapeSimText` of `wfIn_spec`
  and `wfInBy_spec` (`escape_sim_spec` needs StepGaps, false at text-changing escapes until StepGaps.phCall is
  restated). `Host.WFIn.escapeBehaviour` quantifies over a `rer` that is a Record of the six RegExp Record fields,
  its five flags Booleans (`RerFields`, `RerFlags`), with `rer`, `input` and the cells they reach allocated
  (`ReachAlloc`): *"(?:)"*'s CompileAtom reads the flags (UpdateModifiers) and the empty pattern's does not, and a
  dangling `input` stops one but not the other; the patterns are evaluated as RegExp objects, whose
  [[RegExpRecord]] has every field, the flags Booleans (RegExpInitialize), and whose matcher RegExpBuiltinExec
  calls on a fresh List.
- scope: RegExp.prototype.source on the default test hosts.
- decided: coordinator 2026-10-15 (merge f63b44144 round-k); FastHost's answer: user 2026-10-16 (option B,
  esl-escape-pattern); RefHost's answer under the Pattern check with `EscapeSim`: user 2026-10-21 (#20406, option a
  of #20387, t262-escape-land); `RerFields`, `RerFlags`, `ReachAlloc`: coordinator 2026-10-22 (#14990, #15183,
  #21593, esl-escape-pattern-a)
- covers:
  - host EscapePattern
- report: -

## host-defined-operations
- spec: sec-hosts-and-implementations (spec.html 303); sec-host-hooks-summary (spec.html 54778)
- quote: A host-defined facility is one that defers its definition to an external source without further qualification
- text: Host-defined operations have no body in the text.
- decision: An algorithm the data has no body for is a host hook; an unknown clause stops as residue.
- scope: every host.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent knotCall
- report: -

## resizable-buffers
- spec: sec-hostresizearraybuffer (spec.html 45340-45359); sec-hostgrowsharedarraybuffer (spec.html 45947-45970)
- quote: It gives the host an opportunity to perform implementation-defined resizing of _buffer_. … It gives the host an
  opportunity to perform implementation-defined growing of _buffer_.
- text: The hosts may handle a resize themselves.
- decision: ~unhandled~: the spec's own steps resize.
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent hooks (HostResizeArrayBuffer)
  - silent hooks (HostGrowSharedArrayBuffer)
- report: -

## math-random
- spec: sec-math.random (spec.html 33593-33597)
- quote: chosen randomly or pseudo randomly with approximately uniform distribution over that range, using an
  implementation-defined algorithm or strategy.
- text: The value is implementation-chosen, "random or pseudo random". `Host.WF.mathRandom` states what is fixed: a
  Number with positive sign in [+0, 1), never an abrupt completion, the state left as it is. The distinct-Realms
  sentence (spec.html 33596) is `Host.WF.mathRandomRealms`: each logged call carries the running Realm, and along a
  run's growing logs two Realms that call Math.random without end answer apart at some call of the same number. The
  distribution sentence ("approximately uniform") is loose: no finite trace refutes it, and no law states it.
- decision: +0, a test host's answer (the seeded host: a multiple of 2^-53 drawn from its seed, other than ½), except
  ½ at the Realm's call numbered one past the log position of its first call (`realmMark`): distinct Realms have
  distinct first positions, so their sequences differ there.
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent hooks (Math.random)
- report: -

## locale-sensitive-methods
- spec: sec-string.prototype.tolocaleuppercase (spec.html 36646-36655); sec-string.prototype.tolocalelowercase
  (spec.html 36635-36644); sec-string.prototype.localecompare (spec.html 36128-36173);
  sec-number.prototype.tolocalestring (spec.html 32833-32838); sec-bigint.prototype.tolocalestring (spec.html
  33334-33339); sec-date.prototype.tolocaledatestring (spec.html 35426-35431); sec-date.prototype.tolocalestring
  (spec.html 35433-35438); sec-date.prototype.tolocaletimestring (spec.html 35440-35445);
  sec-properties-of-the-date-prototype-object (spec.html 34845); sec-%typedarray%.prototype.tolocalestring
  (spec.html 42881-42892)
- quote: An ECMAScript implementation that includes the ECMA-402 Internationalization API must implement this method as
  specified in ECMA-402. Otherwise, the following specification of this method is used:
- text: Without ECMA-402 the locale-sensitive result is the implementation's: toLocaleUpperCase and
  toLocaleLowerCase work "exactly the same as" toUpperCase and toLowerCase but for the host locale's rules,
  localeCompare's comparison is implementation-defined (a consistent total ordering honouring canonical
  equivalence), Number's and BigInt's toLocaleString may return toString's String, and Date's three methods return an
  implementation-defined String "intended to represent" the Date, its "date" portion or its "time" portion. No
  method uses the optional parameter positions. Date's methods are not generic: the *this* value "must be an object
  that has a [[DateValue]] internal slot", and the text gives no consequence for any other value. %TypedArray%'s
  toLocaleString is described in prose only: Array.prototype.toLocaleString's algorithm with TypedArrayLength for
  the [[Get]] of *"length"*, after ValidateTypedArray(*this*, ~seq-cst~); its separator is implementation-defined.
- decision: Host choices (LocaleUppercase, LocaleLowercase, LocaleCompare, LocaleNumberString, LocaleDateString;
  laws Host.WF.localeCase, localeCompare, localeNumberString, localeDateString). LocaleDateString gives a String or
  ~empty~ (the non-locale form: toDateString's, toTimeString's or toString's) for an object with a [[DateValue]]
  slot, and a String or ~throw~ (a *TypeError*) for any other *this* value: the reading of "not generic" that every
  algorithmic Date method follows, as a bound (D3). Loose: the case mappings' locale exceptions, the comparison's
  order and magnitude, every String's contents, and whether a non-Date *this* gives a TypeError or a String. The
  test hosts answer as a locale with no rules of its own: toUppercase and toLowercase, -1, +0 or 1 by the code point
  order of the canonical decompositions (NFD), ~empty~ (toString's String), and for Date ~empty~ (the forms of
  toDateString, toTimeString and toString, in UTC: row time-zones) and ~throw~ for a non-Date *this*. %TypedArray%.prototype.toLocaleString is an overlay algorithm: those steps, with the
  host choice ListSeparator (row other-host-choices) as the separator; the clause's optimisation sentence is advice.
  ECMA-402 itself stays outside the base layer (scope).
- scope: the default test hosts (FastHost, RefHost).
- decided: user 2026-10-16 ("Yes, host choice"; brief esl-tolocale-host); user 2026-10-17 (#7168, the host
  rule); D3: a non-Date *this* gives a TypeError or a String (coordinator, decision_log; plan #7291)
- covers:
  - host LocaleUppercase
  - host LocaleLowercase
  - host LocaleCompare
  - host LocaleNumberString
  - host LocaleDateString
  - reading definition-sec-string.prototype.localecompare-4
  - overlay formal-string.prototype.tolocaleuppercase
  - overlay formal-string.prototype.tolocalelowercase
  - overlay formal-number.prototype.tolocalestring
  - overlay formal-bigint.prototype.tolocalestring
  - overlay formal-date.prototype.tolocalestring
  - overlay formal-date.prototype.tolocaledatestring
  - overlay formal-date.prototype.tolocaletimestring
  - overlay formal-%typedarray%.prototype.tolocalestring
- report: -

## execution-resources
- spec: sec-preparefortailcall (spec.html 26268-26281); sec-agent-clusters (spec.html 12496-12498);
  sec-ecmascript-function-objects-call-thisargument-argumentslist 7 (spec.html 13508)
- quote: must either release any transient internal resources associated with the currently executing function execution
  context
- text: A tail position call "must either release any transient internal resources associated with the currently
  executing function execution context ... or reuse those resources". Beyond the embedding's freedom to terminate
  an agent, the text says nothing else about resources or running out of them. The execution context stack keeps a
  tail call's discarded context until its [[Call]] returns.
- decision: Resources are a host feature. A host may stop a run at an implementation limit (implLimit) only when it
  pushes an execution context while the contexts on the stack whose resources were not discarded
  (DiscardContextResources) exceed a bound fixed for that host (Host.exhausts; law Host.WF.contextResources, over
  liveContexts). A chain of tail calls does not raise that count, so its length never reaches the limit. It may
  also stop a run at an implementation limit when it allocates an object (MakeBasicObject's MakeObject) while the
  allocated heap cells exceed a bound fixed for that host (Host.exhaustsHeap, read with Host.allocL; law
  Host.WF.heapResources, over CellsAbove): the embedding's termination of a runaway agent (spec.html 12496-12498).
  Mid-job termination happens only at such a push or allocation. Loose: the bounds. Termination between jobs is the
  host's next-job answer none: the job loop logs it as `next none` only where every Job scheduled (a hook whose first
  argument is an Abstract Closure: generic, promise and timeout jobs; cleanup jobs run "if possible") has been taken
  (`drained`), else as `terminate`, the embedding's termination of the agent (`nextCall`). The test hosts have no
  bound (exhausts and exhaustsHeap are false).
- scope: every host (the law); the default test hosts, FastHost and RefHost (no bound).
- decided: user 2026-10-17 (#7168, the host rule); coordinator 2026-10-18 (decision_log 86: implLimit only at a
  push, over a host-fixed bound on contexts not discarded; the embedding's termination and heap exhaustion stay
  loose); user 2026-10-18 (#9576, model-audit H4: implLimit also at an allocation, over a host-fixed
  bound on allocated cells); user 2026-10-20 (#9576, model-audit H3: termination between jobs logged as `terminate`)
- covers:
  - host DiscardContextResources
- note: The executor's fuel (the knot's depth) is not a host feature: a tail call takes about 30 levels, as a non-tail
  call does, and an outOfFuel or timeout on a tail-call-optimization test is an executor limit, not a finding.
- report: -

## time-zones
- spec: sec-getnamedtimezoneoffsetnanoseconds (spec.html 34142-34160); sec-availablenamedtimezoneidentifiers
  (spec.html 34192-34220); sec-systemtimezoneidentifier (spec.html 34222-34244)
- quote: The returned integer represents the offset from UTC, in nanoseconds, of the named time zone identified by
  _timeZoneIdentifier_
- text: Time zones, their rules and names are the implementation's.
- decision: UTC only: offset 0, no local political rules, the one identifier *"UTC"* and no non-primary ones, no
  transitions, system zone "UTC", empty name suffix.
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults; merge cfe4a589d round-h)
- covers:
  - silent hooks (GetNamedTimeZoneOffsetNanoseconds)
  - silent choice (time zones)
  - silent choice (TimeZoneNameSuffix)
  - silent choice (SystemTimeZoneString)
  - host SupportsOnlyUTC
  - host HasTimeZoneRules
  - host AvailableNamedTimeZoneIds
  - host IsNonPrimaryTimeZoneId
  - host LastTransitionBefore
  - host TimeZoneNameSuffix
  - host SystemTimeZoneString
- report: -

## jobs
- spec: sec-jobs (spec.html 12140-12328); sec-runtime-semantics-scriptevaluation (spec.html 26446-26477)
- quote: Jobs are scheduled for execution by ECMAScript host environments in a particular agent.
- text: When and in which order jobs run, with which realm, and what a host does after an abrupt script, are the
  host's within §9.5's requirements.
- decision: The enqueue call is the queue entry; generic and promise jobs in scheduling order, then timeout jobs (one
  due at or past the time value limit stops at the implementation limit: test-host-clock); a null-realm job pushes no
  context; a top-level abrupt completion ends the run before queued jobs.
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent hooks (job enqueue)
  - silent nextJob
  - silent prepareJob
  - silent inJob
  - silent program
- report: -

## approximations
- spec: sec-hosts-and-implementations (spec.html 296); sec-function-properties-of-the-math-object (spec.html 33173);
  sec-setfunctionname (spec.html 13851)
- quote: An implementation-approximated facility is one that defers its definition to an external source while
  recommending an ideal behaviour.
- text: Implementation-approximated values and other host choices among values that the text leaves open.
- decision: The exact value converted with 𝔽 (FastHost; RefHost's stops); an integer itself; of two Strings the second,
  else the first.
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent choice (Approx)
  - silent choice (ApproxInteger)
  - silent choice (HostChoice)
  - host Approx
  - host ApproxInteger
  - host HostChoice
- report: -

## other-host-choices
- spec: sec-localizedlistseparator (spec.html 41501-41507); sec-dowait (spec.html 47153); sec-atomics.pause
  (spec.html 47446-47462); sec-createbytedatablock (spec.html 4486-4500);
  sec-debugger-statement-runtime-semantics-evaluation (spec.html 23518-23530); sec-initializehostdefinedrealm
  (spec.html 11816-11845)
- quote: It returns an implementation-defined String appropriate for use as a list separator in the host
  environment's current locale … Let _additionalTimeout_ be an implementation-defined non-negative mathematical value.
- text: Implementation-defined values the text constrains only by type or range.
- decision: ", " separator; no added timeout; no pause or resource hint; allocation up to 2^32 bytes; no debugger
  (RefHost's DebuggerAction does nothing); ~empty~ global object, this value and cleanup cell; no built-in
  context initialization (the global properties: test-host-global-properties).
- scope: the default test hosts.
- decided: coordinator 2026-10-15 (commit 89d31f730 ss-defaults)
- covers:
  - silent choice (HostInitializeBuiltinContext)
  - silent choice (AdditionalTimeout)
  - silent choice (SpinWaitHint, DiscardContextResources)
  - silent choice (CanAllocate)
  - silent choice (DebuggerEnabled)
  - silent choice (HostGlobalObject, HostThisValue, MayCleanup)
  - silent choice (HostReportCleanupError)
  - host HostInitializeBuiltinContext
  - host AdditionalTimeout
  - host SpinWaitHint
  - host CanAllocate
  - host DebuggerEnabled
  - host DebuggerAction
  - host HostGlobalObject
  - host HostThisValue
  - host MayCleanup
  - host HostReportCleanupError
- report: -

## test-host-global-properties
- spec: sec-initializehostdefinedrealm 17 (spec.html 11842); sec-detacharraybuffer (spec.html 45275);
  sec-initializehostdefinedrealm (spec.html 11816-11845); sec-parse-script (spec.html 26423-26444);
  sec-runtime-semantics-scriptevaluation (spec.html 26446-26469)
- quote: Create any host-defined global object properties on _global_.
- text: Which properties the host creates on the global object is host-defined; test262's INTERPRETING.md asks for
  `print` and `$262` (`global`, `detachArrayBuffer`: DetachArrayBuffer with the key *undefined*, `createRealm`: a new
  realm with this API on its global object, returning its `$262`, `evalScript`: ParseScript in the current Realm, the
  first error thrown, then ScriptEvaluation, among others).
- decision: The test host's HostGlobalProperties (FastHost.globalProps) adds `print` (writable, enumerable,
  configurable) and `$262` (writable, configurable) to _global_ where it has no property of that key. Each function
  is a new built-in function object made like the realm's %isNaN% (its slots, [[Behaviour]] the host's algorithm,
  *"length"* 1, *"name"* its name); `$262` is a new object made like %Reflect%, with *"global"* (_global_),
  *"detachArrayBuffer"*, whose algorithm throws a *TypeError* for a non-ArrayBuffer or a SharedArrayBuffer, then
  performs DetachArrayBuffer(_buffer_) and returns *null*, and *"createRealm"* (*"length"* 0), whose algorithm
  (FastHost.createRealmBuiltin) performs InitializeHostDefinedRealm(), removes the execution context it pushed and
  restores the caller's as the running one, then returns ? Get(_realm_.[[GlobalObject]], *"$262"*) of the new
  realm, whose `$262` comes from this same step 17; the well-known symbols and the Agent Record (its
  [[GlobalSymbolRegistry]]) are shared, and *"evalScript"* (FastHost.evalScriptBuiltin), which throws a
  *TypeError* for a non-String (INTERPRETING.md asks only for a String), then performs ParseScript(_sourceText_, the
  current Realm Record, *undefined*), returns a throw completion of the first error of a List of errors, else
  Completion(ScriptEvaluation(_s_)); *"IsHTMLDDA"* where the host supports §B.3.6 (test-host-is-html-dda). The law
  (Host.WF.hostGlobalProperties): only _global_'s
  own properties change, its slots kept, and new cells may be made. RefHost adds nothing.
- scope: the FastP test host (ecma-run); the spec layer is unchanged.
- decided: coordinator 2026-10-18 (arc/plans/esl-full-scope.md, slices 1-3: esl-262-base, esl-262-createrealm,
  esl-262-evalscript)
- covers:
  - silent choice (HostGlobalProperties)
  - host HostGlobalProperties
- report: -

## test-host-is-html-dda
- spec: sec-IsHTMLDDA-internal-slot (spec.html 54681-54693); sec-initializehostdefinedrealm 17 (spec.html 11842)
- quote: An [[IsHTMLDDA]] internal slot may exist on host-defined objects. … Objects with an [[IsHTMLDDA]] internal
  slot are never created by this specification. … Create any host-defined global object properties on _global_.
- text: The text creates no object with the slot and leaves which host-defined objects have one to the host;
  test262's INTERPRETING.md asks for `$262.IsHTMLDDA`, "present only in implementations that can provide it": an
  object with an [[IsHTMLDDA]] internal slot that returns *null* when called with no arguments or with *""* as its
  first argument. Its other calls, its *"name"* and its *"length"* are unsaid.
- decision: Where the host is a web browser or otherwise supports §B.3.6 (`--web-browser`, `--annex-b
  sec-IsHTMLDDA-internal-slot`: FastHost.ddaBy), HostGlobalProperties gives `$262` *"IsHTMLDDA"* (writable,
  configurable) in every realm, `$262.createRealm()`'s included: a new built-in function object made like the
  realm's %isNaN% with an [[IsHTMLDDA]] internal slot (*undefined*), *"length"* 0 and *"name"* *"IsHTMLDDA"*
  (FastHost.htmlDDA), whose algorithm (FastHost.isHTMLDDABuiltin) returns *null* for every argument list. Its
  internal methods are a built-in function's, so it is not exotic. Elsewhere `$262` has no *"IsHTMLDDA"*.
- scope: the FastP test host (ecma-run); the spec layer is unchanged; RefHost adds
  nothing.
- decided: coordinator 2026-10-20 (decision_log 263; brief esl-host-ishtmldda, finding #10327)
- covers:
  - host HostGlobalProperties
  - code Engine.Host.htmlDDA
  - code Engine.Host.ddaProps
  - code Engine.Host.isHTMLDDABuiltin
  - code Engine.Host.ddaBy
- note: tests/run/is_html_dda.js (`--web-browser`: falsy, typeof *"undefined"*, == *null*, the call's *null*, a
  `$262.createRealm()` realm's own) and is_html_dda_absent.js (absent on the default host).
- report: -

## test-host-module-loader
- spec: sec-HostLoadImportedModule (spec.html 29219-29237); sec-hostgetsupportedimportattributes (spec.html 29292-29306)
- quote: An implementation of HostLoadImportedModule must conform to the following requirements: … It allows host
  environments to specify which import attributes they support.
- text: The loading process is host-defined: which Module Record a (referrer, specifier, attributes) triple maps to,
  how a specifier is normalized, and when loading fails, constrained only by the requirements list (one
  FinishLoadingImportedModule per call; the same normal result for the same referrer and equal request; for a
  *"type"* attribute *"json"*, ParseJSONModule's Completion Record or a throw completion). Which import attributes
  the host supports is host-defined (the default: none).
- decision: The test host's HostGetSupportedImportAttributes answers « *"type"* ». Its HostLoadImportedModule is a
  host algorithm (Spec.Host.hostProg): the key is the specifier and the *"type"* attribute's value, or ~empty~ for
  none (any referrer); a key mapped before gives its Module Record (the map is the host-call log, its earliest
  entry); else the run's module sources (ecma-run --module-dir: each `*_FIXTURE.js` and `*_FIXTURE.json`, and each
  `.js` or `.json` file there that the program or a module it reaches names, as `./NAME`, per test262
  INTERPRETING.md) give, for *"json"*, Completion(ParseJSONModule(source)), its normal value added to the map; for
  another type, a throw completion of a new *TypeError*; for none, ParseModule's record in the current Realm, added
  to the map, or a throw completion of its first SyntaxError. A specifier with no source is a throw completion of a
  new *TypeError*. FinishLoadingImportedModule follows synchronously.
- scope: the FastP test host (ecma-run); the spec layer is unchanged; RefHost keeps the default (empty).
- decided: coordinator 2026-10-17 (briefs/fixup/esl-host-load.md); coordinator 2026-10-18 (arc/plans/esl-full-scope.md,
  slice 5 esl-json-modules)
- covers:
  - file spec/formal/host.emu
  - silent hooks (HostGetSupportedImportAttributes)
- report: -

## test-host-module-run
- spec: sec-example-cyclic-module-record-graphs (spec.html 27751-27755); sec-moduleevaluation (spec.html 27497-27498)
- quote: When a host first calls _A_.LoadRequestedModules()
- text: How a host runs a Module as its entry point is host-defined: the example graphs have the host call
  LoadRequestedModules, Link and Evaluate in turn, but nothing says whether the root's own specifier maps to the
  root's Module Record, nor what the program's outcome is.
- decision: The test host's module run (ecma-run --module, `Engine.Host.Source.module`): ParseModule in the host's
  Realm (its first error a throw completion); HostModuleLoaded(`./NAME`, the record), so that the root imports itself
  by its file name; LoadRequestedModules, whose promise is settled when it returns (the loader is synchronous; a
  rejection is a throw completion of its reason); Link (an abrupt completion ends the run); Evaluate; then the queued
  jobs. The outcome is Evaluate's promise's: rejected, a throw of its reason; fulfilled, *undefined*; pending, the
  promise. `--parse-only` runs ParseModule alone (test262's `parse` negative module tests).
- scope: the FastP test host's program driver (ecma-run); test262's `flags: [module]` tests.
- decided: coordinator 2026-10-17 (briefs/fixup/esl-module-run.md)
- covers:
  - file spec/formal/host.emu
  - code Engine.Host.Source.module
- report: -

## test-host-clock
- spec: sec-date.now (spec.html 34786-34789); sec-date (spec.html 34741-34745); sec-dowait (spec.html 47152);
  sec-hostenqueuetimeoutjob (spec.html 12324); sec-time-values-and-time-range (spec.html 33769)
- quote: Let _now_ be the time value (UTC) identifying the current time. … to be performed after at least _milliseconds_
  milliseconds.
- text: "the time value (UTC) identifying the current time" is the host's; the spec constrains it only to time values
  (and, for DoWait, non-decreasing). HostEnqueueTimeoutJob's job is performed "after at least _milliseconds_
  milliseconds". That time may be set back, so the host law ties the delay to the host's own elapsed time
  (`Host.elapsed`, logged on `next`): it never goes back (`Host.WF.elapsedMono`), and as a timeout job is taken it is
  at least the elapsed time logged before the call plus _milliseconds_ (`Host.WF.timeoutAfter`); a job due past
  8.64 × 10^15 ms has no time value for the time it runs at.
- decision: The default test hosts' clock (FastHost, RefHost, `clockAt`): 1 ms at the first reading, 1 ms more at each
  later one; taking a job moves it to at least the job's due time (the time at its HostEnqueueTimeoutJob call plus
  _milliseconds_ rounded up, `dueAt`), so each later reading is past it; never back, at most the time value limit.
  FastHost stops at the implementation limit (`Stop.implLimit`) where the job it takes is due at or past the limit.
  The test hosts' elapsed time is that clock's as they take a job (`clockElapsed`), and their next job is checked
  against the laws (`checkElapsed`, else the implementation limit). Every test host's TimeNow is `readClock`, which
  also stops at the implementation limit where a reading is below a taken timeout job's due time. The seeded clock (--host-seed) is `timeAt`, about 1 s a host
  call, plus the default clock's time, so a taken job moves it to at least its due time too; its job order is its own,
  and it never takes a timeout job due past the limit from its call's `timeAt`, so the run ends with that job pending.
  A busy-wait on Date.now ends.
- scope: the default test hosts; the spec layer is unchanged.
- decided: coordinator 2026-10-16 (briefs/fixup/esl-host-clock.md, finding #3818: the clock); user 2026-10-17 (#5601:
  Stop.implLimit, the implementation limit as 19.6's reading; finding #5511)
- covers:
  - silent choice (TimeNow)
  - silent nextJob
  - host TimeNow
- report: docs/spec-issues/19-other-questions.md (19.6: a clock past the last time value stops at the
  implementation limit)

## nan-encoding
- spec: sec-numerictorawbytes 1.a-3.a (spec.html 45543-45547)
- quote: _rawBytes_ may be set to any implementation chosen IEEE 754-2019 binary16 format NaN encoding. An
  implementation must always choose the same encoding for each
- text: "may be set to any implementation chosen … NaN encoding. An implementation must always choose the same
  encoding for each implementation distinguishable NaN value": the latitude and its "each" are unclear.
- decision: One host-chosen encoding per format (NaNEncoding), the same each time; the default host's is the
  canonical quiet NaN.
- scope: storing NaN into Float16/32/64 arrays and DataViews.
- decided: coordinator 2026-10-13 (merge 0ba8ab50e ieee-nan2)
- covers:
  - reading definition-sec-numerictorawbytes-1.a
  - reading definition-sec-numerictorawbytes-2.a
  - reading definition-sec-numerictorawbytes-3.a
  - silent choice (NaNEncoding)
  - host NaNEncoding
- report: docs/spec-issues/27-numerictorawbytes-encoding-steps.md, SHORTLIST 14 (upstream: issue #3567, open)

## host-choices-without-laws
- spec: sec-invariants-of-the-essential-internal-methods (spec.html 2911); sec-cleanup-finalization-registry 3-3.a
  (spec.html 12699-12700); sec-debugger-statement-runtime-semantics-evaluation 1-1.a (spec.html 23525-23526);
  sec-host-cleanup-finalization-registry 2 (spec.html 12649)
- quote: An implementation must not allow these invariants to be circumvented in any manner … an implementation may
  perform the following steps: … Perform an implementation-defined debugging action. … perform any host-defined steps
  for reporting the error.
- text: §6.1.7.3 constrains only what the essential internal methods report, and the text puts no other bound on what a
  host step may change. Three overlay entries pass a choice the text leaves open to a host primitive whose law is not
  just the text's constraint: MayCleanup has its law (`mayCleanup`), but the model has no collector, so no run reaches
  the step with a cell to give (C1); DebuggerAction and HostReportCleanupError are bounded by the host frame below.
- decision: A host step keeps to a frame stricter than §6.1.7.3: it changes only the heap, each object as §6.1.7.3
  allows and no other internal slot or cell. Every internal slot but [[Extensible]] and [[Prototype]] stays as it was
  (`objKept`), and every cell that is not an object or a property's attribute Record (Lists, Data Blocks, Environment
  Records) stays as it was (`heapKept`), but for the cells and slots a host-defined operation is given to change
  (`hookFree`, `hookSlots`). It binds the host-defined operations (`hookFrame`), the host choices without a law of their
  own on the state, HostReportCleanupError among them (`choiceFrame`), the job steps (`nextJobFrame`,
  `clearsKeptFrame`, `prepareJobFrame`, `cleanupJobFrame`), and DebuggerAction at its objects (`debuggerAction`). A
  host keeps its own state outside the model's State. MayCleanup's entry returns to readings-restating.txt with C1.
- scope: every host: its hooks, choices and job steps.
- decided: coordinator 2026-10-18 (readings audit #9128 §6, G10); the frame: coordinator 2026-10-20 (task
  ma-host-frame-c, review of ma-host-frame-b note 2)
- covers:
  - reading definition-sec-cleanup-finalization-registry-3
  - reading definition-sec-debugger-statement-runtime-semantics-evaluation-1
  - reading definition-sec-host-cleanup-finalization-registry-2
  - code Ecma.objKept
  - code Ecma.Host.OptionalLaws.debuggerAction
- report: -

## agent-record-choices
- spec: sec-agents (spec.html 12350-12407)
- quote: The choice is implementation-defined and should be the alternative that is most efficient for the
  implementation. … Determines whether the agent can block or not. … The values of [[LittleEndian]], [[Signifier]],
  [[IsLockFree1]], [[IsLockFree2]], and [[IsLockFree8]] cannot change.
- text: The Agent Record's [[LittleEndian]] and [[IsLockFree1]], [[IsLockFree2]], [[IsLockFree8]] are
  implementation-defined, and whether the agent can block ([[CanBlock]]) is the host's; the text fixes only their types
  and that the first four cannot change.
- decision: The driver builds the Agent Record before the machine runs (newAgent). Two laws hold it to Table 29:
  AgentRecordOk gives the initial values and one Agent Events Record whose [[AgentSignifier]] is [[Signifier]]
  (init_agentOk proves it of the Fast host's init), and Host.WF.agentFixed keeps the fields that cannot change, and
  [[GlobalSymbolRegistry]], across every host step. [[LittleEndian]], [[CanBlock]] and [[IsLockFreeN]] stay open host
  choices: the test hosts answer [[LittleEndian]] true, [[CanBlock]] false and every [[IsLockFreeN]] true, for the
  whole run.
- scope: the default test hosts (FastHost, RefHost).
- decided: coordinator 2026-10-18 (readings audit #9128 §8; model-audit R12); user 2026-10-20 (#9576, R12's
  laws)
- covers:
  - code Engine.Host.newAgent
  - code Ecma.Host.ChangeLaws.agentFixed
- report: -

## suspend-agent-until
- spec: sec-suspendthisagent 7 (spec.html 47050); sec-agentcansuspend (spec.html 12430-12437); sec-dowait 12
  (spec.html 47128)
- quote: suspend the surrounding agent until the time is _waiterRecord_.[[TimeoutTime]] … Return
  _agentRecord_.[[CanBlock]]. … If _mode_ is ~sync~ and AgentCanSuspend() is *false*, throw a *TypeError* exception.
- text: How long a suspended agent waits, and so when it wakes, is the host's: the text says "until the time is" a
  timeout, an extended mathematical value in milliseconds, without tying it to the host's clock; whether the agent
  can block ([[CanBlock]]) is the host's too.
- decision: The default test hosts' surrounding agent cannot block (DoWait 12 throws), unless the run asks
  (`--can-block`, which test262-runner passes for a CanBlockIsTrue test). SuspendAgentUntil only registers the
  suspension: on the default test hosts (FastHost, RefHost, `suspendUntil`) it answers ~unused~ with the state
  unchanged, on a time or +∞, and the logged call is the suspension that AgentWoken, AgentTimeout and HostSelectAgent
  read (`pendingAt`). The wait is step 7's AgentInterleave loop. The default clock (`Clock.step`) moves at
  AgentTimeout, to at least its answer rounded up to a millisecond (row agent-timeout), and by 1 ms at each selection
  of an agent, so a later Date.now is not before a wake; the seeded clock (--host-seed) adds the default clock's time,
  so a wake moves it too. Host.WF's suspendAgentUntil row holds every host to this answer.
- scope: the default test hosts.
- decided: coordinator 2026-10-18 (task esl-canblock-host, briefs/handoff-round-20.md; for review)
- covers:
  - host SuspendAgentUntil
  - code Ecma.suspendUntil
  - code Ecma.Clock.step
  - code Engine.Host.HostOpts.canBlock
- report: -

## agent-interleaving
- spec: sec-forward-progress (spec.html 12518-12528)
- quote: every unblocked agent with a dedicated executing thread eventually makes forward progress … in a set of agents
  that share an executing thread, one agent eventually makes forward progress
- text: The text lets agents run in parallel or share an executing thread, and asks only that agents eventually make
  forward progress; it does not say where one agent's evaluation steps may interleave with another's.
- decision: The agents of a cluster share one executing thread and switch cooperatively, only at AgentInterleave
  (overlay formal-agent-interleave): the host's HostSelectAgent picks the agent that runs next, SwitchToAgent parks
  the surrounding agent's execution context stack in its [[ParkedStack]] and installs the target's, and a Resume
  continues the target where it last switched. AgentInterleave is performed at SuspendThisAgent step 7's wait loop
  and at the four shared reads with several Agent Events Records (sab-single-agent-reads), never inside a critical
  section, so AcquireCriticalSection's one-agent meaning stays exact; the other scheduling points (the $262.agent
  functions, main's idle loop) come with a multi-agent host. With sequentially consistent shared reads,
  every finer interleaving is observably the same, except that an agent looping forever with no scheduling point
  starves the others: the run stops out of fuel where the text's forward progress would let them finish.
- scope: such loops (an agent's loop with no shared read, host call or wait); no full.conf test has one.
- decided: user 2026-10-20 (#11024, answer a: cooperative switch points)
- covers:
  - overlay formal-agent-interleave
  - code Ecma.Prims.Context.switchToAgent
- report: -

## agent-fairness
- spec: sec-forward-progress (spec.html 12518-12528)
- quote: in a set of agents that share an executing thread, one agent eventually makes forward progress
- text: For agents that share an executing thread the text asks only that one of them eventually make forward
  progress; it does not say whether each runnable agent must eventually be selected, and "eventually" bounds nothing
  a single host call can be held to.
- decision: Host.WF's selectAgent row holds every host to a per-call law: ~empty~, or an Agent Record whose
  [[Signifier]] is one of the cluster's [[AgentSignifier]]s and not the surrounding agent's, other than the
  surrounding agent, that can run. Suspensions are keyed by Agent Record and wakes by signifier, so the law needs no
  relation between an agent's signifier and its Record (sorts: the signifier is opaque); with AgentTimeout it gives
  the text's one-agent progress. FastHost's HostSelectAgent is round-robin over the cluster's [[EventsRecords]] order
  after the surrounding agent's signifier (selectNext; its signifiers are its Agent Records), and proves the
  stronger per-call law selectNext_fair: it passes over only agents it cannot switch to (`switchable`), and answers
  ~empty~ only where it can switch to none. Since SwitchToAgent installs the selected agent, an agent that can run at
  each of B consecutive selections, B the cluster's size, is selected among them. Bounded fairness is FastHost's
  choice, not a Host.WF row: RefHost has one agent and answers ~empty~.
- scope: FastHost's clusters ($262.agent); the multi-selection bound is stated over the per-call law, not proved over
  drive's runs.
- decided: coordinator 2026-10-20 (task esl-agents-cluster, arc/plans/esl-agents.md D-2 laws; for review)
- covers:
  - host HostSelectAgent
  - code Ecma.selectNext
  - code Ecma.switchable
  - code Ecma.Host.JobLaws.selectAgent
- report: -

## choose-reads-bytes-from
- spec: sec-reads-bytes-from (spec.html 53041-53046); sec-valid-chosen-reads (spec.html 53138-53149)
- quote: its reads-bytes-from function is a mathematical function mapping Memory events … Each event _writeEvent_ with
  index _i_ in _writes_ has _readEvent_.[[ByteIndex]] + _i_ in its memory range.
- text: The memory model admits every candidate execution with a valid execution; for a multi-agent read it does not
  say which write events the read reads from, and a host may answer any choice the valid-execution conditions allow.
- decision: ChooseReadsBytesFrom is the host's choice of a read's reads-bytes-from: a List of _elementSize_ write
  events, one per byte. Host.WF's chooseReadsBytesFrom (law L1) holds every host to a new List of that length whose
  element j is an event of the execution's [[EventList]]s that writes byte _byteIndex_ + j of the block. FastHost
  answers the sequentially consistent execution (scWrites): each byte's latest write in the interleaving order,
  rebuilt from the log's HostSelectAgent cuts (each logged _n_ ends an agent's segment of its [[EventList]]); a
  byte no event wrote is residue. RefHost has one agent and answers residue.
- scope: FastHost's clusters. Host.WF's chooseReadsValid (law L2) holds every host to a choice that keeps a valid
  execution valid where its memory order is the interleaving order; FastHost's latest writes do
  (Ecma.MemoryModel.scWrites_valid), RefHost answers residue. L2's restriction
  to executions whose memory order agrees with the interleaving order is deliberate: the run-level form (the
  execution's validity with its own reads-bytes-from witnesses as the only premise) needs a whole-run invariant of
  each host, so after a read no such memory order explains (a weak-memory host's) L2 binds no later read, and L1
  alone holds. Its claim is not vacuous where the writes are total (ModifyOp totality).
- decided: coordinator 2026-10-20 (arc/plans/esl-agents.md D-2, D-3; task esl-agents-reads; for review)
- covers:
  - host ChooseReadsBytesFrom
  - code Ecma.scWrites
  - code Ecma.Host.MemoryLaws.chooseReadsBytesFrom
  - code Ecma.Host.MemoryLaws.chooseReadsValid
  - overlay formal-choosesharedbytes
- report: -
## agent-timeout
- spec: sec-suspendthisagent 7 (spec.html 47050); sec-forward-progress (spec.html 12518-12528)
- quote: suspend the surrounding agent until the time is _waiterRecord_.[[TimeoutTime]] … in a set of agents that
  share an executing thread, one agent eventually makes forward progress
- text: The text does not say how the time passes while every agent of a cluster that shares an executing thread is
  suspended, nor when a suspension with an infinite timeout and no notification ends.
- decision: AgentInterleave performs the host primitive AgentTimeout where HostSelectAgent answers ~empty~. The
  default test hosts (FastHost, RefHost, `agentTimeout`) answer the time now where the surrounding agent can run, else
  the earliest wake by a timeout of the Agent Records suspended in the log (`suspendedAgents`), not before now; the
  default clock (`Clock.step`) moves to
  that time rounded up to a millisecond. Where no agent wakes by a timeout (+∞, or past the last time value) it stops
  out of fuel. Host.WF's agentTimeout row holds every host to this answer.
- scope: the default test hosts; with one agent, the wait of SuspendThisAgent step 7.
- decided: coordinator 2026-10-20 (#16392, arc/plans/esl-agents.md D-2; for review)
- covers:
  - host AgentTimeout
  - code Ecma.agentTimeout
  - code Ecma.agentTimeout
- report: -

## agent-woken
- spec: sec-suspendthisagent 7 (spec.html 47050)
- quote: The surrounding agent can only wake from suspension due to a timeout or due to another agent calling
  NotifyWaiter with arguments _waiterList_ and _thisAgent_
- text: The text does not say how the suspended agent learns that it has been woken.
- decision: Step 7's loop asks the host primitive AgentWoken. The default test hosts (FastHost, RefHost,
  `agentWoken`) answer whether the surrounding agent can run (`runnable`): *true* once a WakeAgent of its signifier
  follows its latest SuspendAgentUntil in the log, or the clock has reached its timeout; never a spurious wake.
  Host.WF's agentWoken row holds every host to this answer.
- scope: SuspendThisAgent step 7.
- decided: coordinator 2026-10-20 (#16392, arc/plans/esl-agents.md D-2; for review)
- covers:
  - host AgentWoken
  - code Ecma.agentWoken
  - code Ecma.agentWoken
- report: -

## wake-agent
- spec: sec-notifywaiter 2.a (spec.html 47068)
- quote: Wake the agent whose signifier is _waiterRecord_.[[AgentSignifier]] from suspension.
- text: The text does not say what waking an agent changes, beyond its resumption in SuspendThisAgent.
- decision: The host primitive WakeAgent answers ~unused~ and leaves the state as it is on the default test hosts
  (FastHost, RefHost): the wake is the logged call itself, which AgentWoken and HostSelectAgent read (`pendingIn`).
  Host.WF's wakeAgent row holds every host to this.
- scope: Atomics.notify of a ~blocking~ waiter.
- decided: coordinator 2026-10-20 (#16392, arc/plans/esl-agents.md D-2; for review)
- covers:
  - host WakeAgent
  - code Ecma.pendingIn
- report: -

## annexb-block-function-hoisting-domain
- spec: sec-functiondeclarationinstantiation (spec.html 14016); sec-globaldeclarationinstantiation (spec.html 26531);
  sec-evaldeclarationinstantiation (spec.html 30283); sec-static-semantics-contains (spec.html 9474-9482)
- quote: that is directly contained in the |StatementList| of any |Block|, |CaseClause|, or |DefaultClause| _x_ such that …
  Contains _x_ is *true*, do … _symbol_: a grammar symbol, … If _child_ is an instance of _symbol_, return *true*.
- text: The web-compat steps of FunctionDeclarationInstantiation, GlobalDeclarationInstantiation and
  EvalDeclarationInstantiation iterate "each FunctionDeclaration that is directly contained in the StatementList of
  any Block, CaseClause, or DefaultClause _x_ such that _P_ Contains _x_". "Directly contained" is not defined; "any"
  names no domain or order for _x_ and the function declarations; and Contains is declared to take a grammar symbol,
  but _x_ is a Parse Node, so its step "_child_ is an instance of _symbol_" has no meaning there.
- decision: The step is a For-each over the List its phrase (ph-annexb-foreach) gives. A node is directly contained in
  a list nonterminal's instance when every node between them has a single child node (FunctionDeclaration through
  HoistableDeclaration, Declaration and StatementListItem; not through a LabelledStatement or another statement), the
  list taken at the outermost of its own recursion (DirectlyContainingList). _x_ ranges over ParseNodesWithin(_P_),
  the only nodes _P_ Contains reaches (annexb-block-function-search-root); the declarations come in source text order.
  "_child_ is an instance of _x_" for a Parse Node _x_ is "_child_ is _x_", so _P_ Contains _x_ holds when Contains's
  walk reaches _x_ (not into nested functions, classes' bodies or arrow functions).
- scope: the three web-compat steps (the host is a web browser: --web-browser); InstanceOf of two Parse Nodes.
- decided: coordinator 2026-10-18 (bus #10267, #10304; finding #9587)
- covers:
  - overlay ph-annexb-foreach
  - overlay formal-directlycontaininglist
  - code Ecma.Prims.Nodes.instanceOf
- report: SHORTLIST 19 (B.3.2's block-function steps)
## host-extension-hooks
- spec: sec-conformance (spec.html 235); sec-error-handling-and-language-extensions (spec.html 29969);
  sec-forbidden-extensions (spec.html 29973-30012); sec-initializehostdefinedrealm 2 (spec.html 11822);
  sec-error-message 5 (spec.html 32190); sec-nativeerror 5 (spec.html 32331); sec-aggregate-error 7 (spec.html
  32719); sec-suppressederror 6 (spec.html 32485)
- quote: a conforming implementation of ECMAScript may provide properties not described in this specification, and
  values for those properties, for objects that are described in this specification. … Perform
  CreateIntrinsics(_realm_).
- text: The text lets a host add properties to the objects it describes (§2, §17, except as §17.1 forbids) but has no
  step where that happens, so a model with none can't express a host that adds any (a `stack` on error objects, a
  non-standard method on an intrinsic).
- decision: Two host hooks. HostExtendIntrinsics(_realm_) runs right after CreateIntrinsics in
  InitializeHostDefinedRealm; HostExtendObject(_o_) runs on each error object the machine creates, before the Error,
  _NativeError_, AggregateError and SuppressedError constructors return it and in "a newly created _name_ object"
  (ph-new-error). Their laws (Host.WF.hostExtendIntrinsics, Host.WF.hostExtendObject): the answer is ~unused~; only
  own properties are added (to any object, or only to _o_), no internal slot, existing property or other cell
  changes, new cells may be made (onlyAdds); no new own *"caller"* or *"arguments"* on an object with a [[Call]]
  (noForbiddenProps). The test hosts (FastHost, RefHost) add nothing and leave the state as it is.
- scope: the spec layer (the hook points) and the default test hosts (their answer).
- decided: coordinator 2026-10-19 (model-audit R10; task ma-choices-r10m7, #9576)
- covers:
  - reading definition-sec-initializehostdefinedrealm-2
  - reading definition-sec-error-message-5
  - reading definition-sec-nativeerror-5
  - reading definition-sec-aggregate-error-7
  - reading definition-sec-suppressederror-6
  - host HostExtendIntrinsics
  - host HostExtendObject
  - code Ecma.onlyAdds
  - code Ecma.noForbiddenProps
- report: -

## job-callback-hooks
- spec: sec-hostmakejobcallback (spec.html 12239-12245); sec-hostcalljobcallback (spec.html 12263-12273)
- quote: It must return a JobCallback Record whose [[Callback]] field is _callback_. … ECMAScript hosts that are not
  web browsers must use the default implementation of HostMakeJobCallback. … It must perform and return the result of
  Call(_jobCallback_.[[Callback]], _thisValue_, _argList_). … ECMAScript hosts that are not web browsers must use the
  default implementation of HostCallJobCallback.
- text: The two host-defined operations have default bodies in the data, so the machine always runs them; the text
  requires the defaults only of hosts that are not web browsers, and lets a web browser set [[HostDefined]] and act
  around the call (HTML's incumbent settings), within the two requirements.
- decision: Readings make the host's parts host primitives and keep the requirements by construction:
  HostMakeJobCallback returns { [[Callback]]: _callback_, [[HostDefined]]: HostJobCallbackData(_callback_) };
  HostCallJobCallback performs HostPrepareCallJobCallback(_jobCallback_), then Completion(Call(…)), then
  HostCleanupCallJobCallback(_jobCallback_), and returns ? the Call's completion. Laws: HostJobCallbackData keeps
  to choiceFrame; the two bracket steps give ~unused~ and change only the heap, the execution context stack and the
  suspended context (Host.WF.callJobCallbackFrame, jobFrame); where every WebBrowser answer in the log is false,
  HostJobCallbackData gives ~empty~ and the bracket steps ~unused~, each leaving the state as it is: the default
  implementations (Host.WF.jobCallbackDefault). The test hosts (FastHost, RefHost, the legacy diff host) answer the
  defaults for every run, web browser or not.
- scope: the spec layer (the hook points) and the default test hosts (their answer).
- decided: coordinator 2026-10-20 (model-audit C2, D3; task ma-host-gc, #9576, #14986)
- covers:
  - reading definition-sec-hostmakejobcallback-1
  - reading definition-sec-hostcalljobcallback-2
  - host HostJobCallbackData
  - host HostPrepareCallJobCallback
  - host HostCleanupCallJobCallback
  - code Ecma.Host.JobLaws.jobCallbackDefault
- report: -

## weakref-collection
- spec: sec-weakref-execution (spec.html 12603-12631)
- quote: At any time, if a set of objects and/or symbols _objSet_ is not live, an ECMAScript implementation may
  perform the following steps atomically … Set _ref_.[[WeakRefTarget]] to ~empty~. … it empties WeakRefs for all
  values in _objSet_ simultaneously.
- text: Collection is the host's, at any time, over any set that is not live; liveness (§9.10.2) quantifies over
  hypothetical WeakRef-oblivious executions and is not decidable.
- decision: At a job boundary, after ClearKeptObjects, where `drive` holds no saved computation (State.saved 0), the
  host's step `collect` runs, logged: it gives a set of objects and Symbols and empties every WeakRef and
  FinalizationRegistry cell whose [[WeakRefTarget]] is one of them, together, nothing else changing. The law
  (Host.WF.collect, Collected): no element is reachable from the roots (the execution context stack, the resumed and
  suspended values, the Agent Record with its [[KeptAlive]], the bookkeeping, the host-call log's values: the
  scheduled jobs and the realms, the WaiterList Records and Shared Data Blocks), counting every cell value but a
  [[WeakRefTarget]] whose target is in the set itself (a WeakRef's edge to a value outside the set keeps it);
  reachability is a sound under-approximation of non-liveness. MayCleanup then has emptied cells to
  give. Loose: collection at other times (within a job, or while a computation is saved, whose Lean locals are not
  roots); a WeakMap's or WeakSet's entries (their keys count as reachable, so no entry is ever emptied); the
  _enqueueCleanup_ choice (no cleanup job is enqueued); sets beyond the reachable bound. The test hosts collect
  nothing (the default `Host.collect`).
- scope: the spec layer (the job boundary) and the default test hosts (their answer).
- decided: user 2026-10-20 (#15060: collection only at a job boundary with no saved computation, model-audit C1;
  task ma-host-gc, #9576)
- covers:
  - code Ecma.Host.collect
  - code Ecma.Host.ChangeLaws.collect
  - code Ecma.Collected
  - code Ecma.collectBoundary
- report: -

## parsejson-result-defined-by
- spec: sec-ParseJSON 8 (spec.html 47592)
- quote: Assert: _result_ is either a String, a Number, a Boolean, an Object that is defined by either an
  |ArrayLiteral| or an |ObjectLiteral|, or *null*.
- text: "An Object that is defined by" a literal is not defined: the text does not say which node defines an Object
  or how a step would find it.
- decision: The checked Assert reads it as: if _result_ is an Object, _script_ Contains |ArrayLiteral| or
  |ObjectLiteral|; otherwise _result_ is a String, a Number, a Boolean or *null*. The only Object a valid JSON text's
  |Expression| has as its value is the one its outermost |ArrayLiteral| or |ObjectLiteral| creates, so the reading
  holds wherever the text's does.
- scope: the checked meaning (Asserts); the unchecked runs do not evaluate it.
- decided: coordinator 2026-10-19 (task esl-open-asserts, arc/plans/tier-completeness.md §3 row 23; for review)
- covers:
  - reading definition-sec-ParseJSON-8
- report: -

## execute-module-linked
- spec: sec-source-text-module-record-execute-module 1 (spec.html 28957)
- quote: Assert: _module_ has been linked and declarations in its module environment have been instantiated.
- text: "Has been linked" and "have been instantiated" are not states the Module Record has: the text records a
  module's progress in [[Status]] and its environment in [[Environment]].
- decision: The checked Assert reads it as: _module_.[[Status]] is one of ~linked~, ~evaluating~, ~evaluating-async~
  or ~evaluated~, and _module_.[[Environment]] is not ~empty~. InnerModuleLinking sets ~linked~ only after
  InitializeEnvironment has set [[Environment]] and instantiated its declarations.
- scope: the checked meaning (Asserts).
- decided: coordinator 2026-10-19 (task esl-open-asserts, arc/plans/tier-completeness.md §3 row 23; for review)
- covers:
  - reading definition-sec-source-text-module-record-execute-module-1
- report: -

## initialize-environment-named-exports
- spec: sec-source-text-module-record-initialize-environment 2 (spec.html 28889)
- quote: Assert: All named exports from _module_ are resolvable.
- text: "Named exports" and "resolvable" are not defined; a name a star export brings in may be ambiguous, and
  GetExportedNames does not raise an error for it.
- decision: The checked Assert reads it as: for each ExportEntry Record _e_ of _module_.[[LocalExportEntries]] and
  [[IndirectExportEntries]], _module_.ResolveExport(_e_.[[ExportName]]) is a ResolvedBinding Record. The names star
  exports bring in are left out.
- scope: the checked meaning (Asserts).
- decided: coordinator 2026-10-19 (task esl-open-asserts, arc/plans/tier-completeness.md §3 row 23; for review)
- covers:
  - phrase ph-named-exports-resolvable
- report: -

## lexical-goal-parse-position
- spec: sec-ecmascript-language-lexical-grammar (spec.html 16545-16547)
- quote: the identification of lexical input elements is sensitive to the syntactic grammar context that is
  consuming the input elements
- text: "Syntactic grammar context" is not defined. It can be read over prefixes (P: what some sentence with the
  tokens before the element permits) or at the parse's own position (C: what the parse being built permits there).
  The two are equal exactly when the note's claim (no context permits both a leading division and a leading
  RegularExpressionLiteral) holds over prefixes.
- decision: C. The classes permitted at a position are those of the parses that agree with the parse before it
  (Tree.nextBits, equality of Tree.cut). Directly after a semicolon §12.10 inserted, P's clause applies (the goal
  before the insertion, the note's "not affected by semicolon insertion").
- scope: the lexical goal of every input element (ParsesText).
- decided: user 2026-10-24 (#24468: Q-GL1 C, Q-GL2 (c))
- covers:
  - code Ecma.Grammar.Tree.nextBits
  - code Ecma.Grammar.PermitsAt
  - code Ecma.Grammar.GoalsAt
- report: -
