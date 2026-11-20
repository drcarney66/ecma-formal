# Filing order

The order in which to file or comment on the reports in this directory, what to strip before filing, and candidates
with no draft yet. Lines are the pinned spec.html, b1eaed82f (main, 2026-11-12); "main?" means check main and the
open issues first.

## Ranked shortlist (strongest first)

1. **03** BuiltinCallOrConstruct's return value: every `Array.fromAsync` call fulfils with undefined.
2. **06** DoWait: a timed-out sync `Atomics.wait` returns "ok" and leaves its waiter; a second wait fails AddWaiter's Assert.
3. **20** CreateDynamicFunction lost AllPrivateIdentifiersValid: `new Function("o","return o.#f")`.
4. **33** CreateIntrinsics step 2 (11857) passes `_async_` in CreateBuiltinFunction's 7th position, which is
   `_prefix_` (14141–14149): read literally, built-in async functions get [[Async]] false and no prefix. Comment on #3534.
5. **04** ExecuteModule never disposes top-level `using`/`await using` in a module with top-level await.
6. **24** CompileToCharSet step 2 calls UnicodeMatchPropertyValue(gc, _s_) before testing _s_: comment on #3586/#3587.
7. ~~**08** IsLooselyEqual 9–10: `!` around ToPrimitive, which can throw.~~ Fixed upstream (8a3e4aae, PR #4067): nothing to file.
8. **01** Number::multiply gives +0 for `+0 × -5`.
9. **23** Races: "not the case that both" is always true for a strict order. Model: literal (RacesNotBoth).
10. **11** `/u` with lastIndex inside a surrogate pair; engines disagree, needs consensus.
11. **21** ZWNJ/ZWJ identity escapes became SyntaxErrors without `u` since Unicode 15.1.
12. **25** Number shifts and bitwiseNOT shift "a Number"; open PR #2274 makes this change: a comment there.
13. **09** EnqueueAtomicsWaitAsyncTimeoutJob can pass a negative delay to HostEnqueueTimeoutJob ("a non-negative
    finite Number"), and its Assert depends on implementation-defined choices.
14. **27** NumericToRawBytes NaN and byte order: comment on #3567.
15. ~~**22** reads-bytes-from's unbound `_result_`. Editorial, one-line PR.~~ Fixed upstream (d8cb8772, PR #4064): nothing to file.
16. **10** `new Date(0).setHours(1e21)`, with MakeDay's "finite time value" (`Date.UTC(275761, 0, -256)`) and sorts-doubts 8–9 (UTC's note needs _t_ past
    the time value range; GetNamedTimeZoneEpochNanoseconds returns counts bounded by 34045): comment on PR #3464.
17. **The only 1-origin List** (37894, "indexed 1 through …") against §6.2.2's 0-based `L[i]`. Editorial. No draft.
17a. **Stale Module Record subclass sentence** (26896) omits Synthetic Module Record (28980, a subclass only
    by 28986's "In addition to the fields"). Editorial, one sentence; no upstream issue. No draft.
18. **Number::toString 5 / toExponential 11.b.i** (10.b.i at 726ec8a42): whether the undetermined last digit is
    implementation-defined or may vary per call. Probably known.
19. **Editorial batch**, one PR each line:
    - inline "NOTE:" after a step (19925, 29548);
    - trailing conditional sentences → steps: CreateByteDataBlock, CreateSharedByteDataBlock (4496, 4511),
      parseFloat (30390), Create(Im)MutableBinding (10461, 10482), SetDefaultGlobalBindings 2.b;
    - RepeatMatcher 4's unordered inline loop (37999); `_TypedArray_` 3's `<code>` intrinsic (43165);
    - "of type Reference" (19252, 18484); Number::unaryMinus 2 → "Return -_number_.";
    - CreateBuiltinFunction 6's redundant [[InitialName]] and its null against a String type;
    - toISOString step 6 is dead; remarks inside steps (glosses, "because …", ToObject's "See …");
    - undefined type phrases: "an initialized RegExp instance" (39801); "Array Iterator Instance" /
      "RegExp String Iterator Object Instance" / "For-In Iterator instance" (41756, 40091, 22859; check
      PR #3976 first); "sequence of Unicode code points" → "List of code points"; 4481's Shared Data Block
      "a data block that …" against the disjoint types (4525);
    - **37** String.prototype.split (36562) passes a List of code units to CreateArrayFromList (test262: one-code-unit Strings);
    - parseInt 11's "a radix-_radixMV_ digit" is only implied by step 14;
    - undefined "contained within" / "contain" (Parse Nodes), "an entry for _x_", "has attribute values";
    - "the derived |X|" (12 uses) is never defined;
    - Assert wording: "valid byte offsets within the memory of", "explicitly defined" undefined;
      "is not ~new~ or ~unlinked~" → "neither … nor"; "ordinary, extensible object" (comma);
    - **52** MV's row for `` DecimalIntegerLiteral :: `0` `` (17235), which PR #3988 left when it removed the
      production;
    - **29** PropName has no row for CoverInitializedName (an editorial report; no erratum of the model);
    - **28** ToBigInt's Boolean row writes `1n`/`0n` as source-text literals and its two cases as one sentence;
    - **42** B.1.1's Module condition names the goal symbol; a reparse within a Module carries the Module context
      (`(a <!--b)`);
    - **43** AllocateSharedArrayBuffer's growable branch passes a Shared Data Block to SetValueInBuffer (45906);
    - B.3.2's block-function steps (14016, 26531, 30283): "directly contained in" is undefined, "any … _x_" names no
      domain or order, and "Contains _x_" passes a Parse Node where Contains takes a grammar symbol (9474);
    - toISOString step 7 (35404) does not choose between `YYYY`'s two forms (34450: "four decimal digits from 0000
      to 9999, or as an expanded year") for a year in 0..9999; test262 requires four digits (15.9.1.15-1.js,
      15.9.5.43-0-4.js). A clarification sentence: four digits in 0..9999, expanded otherwise.
20. **46** A covered Parse Node is outside the tree that covers it: IsInTailPosition is false for
    `return (f(n - 1));` (test262 `language/expressions/tco-pos.js` requires a tail call). With it, "the goal symbol
    of the syntactic grammar" (18366, 18406) and "the syntactic goal symbol" (19388) read per parse make
    `(function () { return import.meta; })` in a Module a Syntax Error (compare 42).
21. **Clarification: §B.3.3 without §B.3.2** (54599). "The semantics of such a synthetic |BlockStatement|
    includes the web legacy compatibility semantics specified in B.3.2" does not say whether a host that supports
    B.3.3 and not B.3.2 applies B.3.2's steps, whose own gate is false there: `function g() { if (true) function
    f() {} return typeof f; }` is *"function"* under one reading, *"undefined"* under the other. Fix: guard the
    sentence with "If the host is a web browser or otherwise supports B.3.2". Doubtful, low. No draft.
22. **35** Contains never finds an |AwaitExpression| through a cover: `async function f(x = await 1) {}` has no
    early error (test262 requires one).
23. **36** IsLabelledFunction tests a |Statement| node for being a |LabelledStatement|: always *false*, so
    `if (1) l: function f() {}` has no early error.
24. **13** NewPromiseReactionJob returns a resolving function's throw completion, against §9.5's normal completion;
    with **47** (an editorial report; no erratum of the model), a *null*-realm Job calls user code, against
    HostEnqueuePromiseJob's note. One issue or two.
25. **44** A lookahead restriction over a semicolon §12.10 inserted: `if (false) let` LF `[a] = 0;` (test262 and the
    engines: a SyntaxError).
26. **45** FinalizationRegistry.prototype.unregister removes cells from the List its For each iterates.
27. **41** Annex B: a first-line `-->` (HTMLCloseComment) is neither a comment nor a token for §5.1.3.
28. **26** Annex B: §B.1.2.1 lost the modifier early errors (`/(?ii:a)/`).
29. **39** Early error rules read "the |n| that is covered by" a cover that covers nothing (a clarification report; no
    erratum of the model).
30. **48** happens-before orders an ~init~ write only before *overlapping* ranges, which excludes equal ranges.
31. **31** Sort: a comparator returning ±∞ is neither consistent nor inconsistent.
32. **49** Annex B: IsCharacterClass has no row for `ClassEscape :: c ClassControlLetter`, so `/[\c1-\c5]/` has none.
33. **50** reads-bytes-from and coherent reads test a byte index against a memory range, which has no [[Block]]:
    a read can take another block's byte. Model: the proposed text (MemoryRangeSameBlock).

Proposed normative change, not a defect, filed apart: **51** a maximum BigInt size (`2n ** (2n ** 40n)`).

Low, recheck upstream first: OrdinarySetWithOwnDescriptor 2.d.i (13132) asserts _receiver_ "does not
currently have" P right after a user-code [[GetOwnProperty]]; with a Proxy receiver it is not checkable
(draft **38**; an editorial report, no erratum of the model).

## Comment upstream instead of filing
- 02 on #3766/#3769 (the example graph); 11 on #2511; 12 on #3435 (its first fix breaks
  RunCallerContext's parameter type); 15 on #3989 (the probe example); 24 on #3586/#3587;
  14 on PR #2695; 27 on #3567; 32 on #1865; 33 on #3534; 40 on PR #2445.
- Fixed at main, nothing to file: 07 (PR #3979), 08 (PR #4067), 22 (PR #4064), 34 (PR #3926).
- #3868 for "is a List of errors" (sorts-doubts 11), with 05; 05 also takes "a newly created *X* object"
  naming no realm (related #1462).
- PR #3464 for 10, MakeDay's "finite time value" and sorts-doubts 8–9.
- #2694 for delete's early error naming OptionalChain productions a UnaryExpression's unit chain cannot
  reach (`delete this?.#x`).

Don't file: the undated "latest Unicode Standard" (Annex D makes it deliberate), 19.3, 19.4, 19.6, 19.7, 19.8.7–8.
Doubtful, low: 05, 19.2, 19.8.1–6, 19.8.9 (LR(2); 9b and 9c have fixes that keep
the language). Not spec issues: sorts-doubts 1, 3, 4, 7, 12, 13.

## Before filing
- Strip the formal-model, Erratum and "Found by crates/spec-gen" lines (the drafts' headers, 19.6, 22, 23, the README
  appendix).
