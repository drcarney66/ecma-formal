# Filing order

The order in which to file or comment on the active specification issues in `docs/spec-issues/` (against pinned `spec.html` `b1eaed82f`, excluding items already fixed upstream before `b1eaed82f` and formalization-only choices).

## Ranked shortlist (highest-impact specification defects first)

1. **03** `BuiltinCallOrConstruct` step 10.b.iii: every `Array.fromAsync` call fulfils with `*undefined*` (open PR #4074).
2. **06** `DoWait`: a timed-out sync `Atomics.wait` returns `*"ok"*` and leaves its waiter in `[[Waiters]]`.
3. **20** `CreateDynamicFunction` omits `AllPrivateIdentifiersValid` on `_body_` and `_params_`: `new Function("o", "return o.#f")` succeeds and trips `MakePrivateReference`'s `Assert:` when called.
4. **60** Annex B.3.2 replacement steps end with `Return ~unused~` instead of `Return ~empty~`, leaking `~unused~` out of `eval("{ function f() {} }")`.
5. **53** `String.prototype.repeat` (`"ab".repeat(2 ** 52)`), `concat`, `+`, and `JoinIndexedProperties` lack a `> 2^53 - 1` *RangeError* step against §6.1.4's `2^53 - 1` String maximum.
6. **56 & 57** Post-ASI `/` lexical goal re-scanning (`let a\n/x/.test("x")`), dynamic-function starting lexical goals, and `for (let a\n a < 1; a++)` header ASI loophole.
7. **33** `CreateIntrinsics` step 2 passes `_async_` in `CreateBuiltinFunction`'s `_prefix_` parameter position (#3534, #4046).
8. **04** `ExecuteModule` never disposes top-level `using`/`await using` in a module with top-level `await` (#4039).
9. **24** `CompileToCharSet` step 2 calls `UnicodeMatchPropertyValue("General_Category", _s_)` before testing `_s_` (#3586/#3587).
10. **01** `Number::multiply` step 6 returns `*+0*𝔽` for `+0 × -5` (open PR #4072).
11. **37** `String.prototype.split` step 10.d passes a List of code units instead of 1-unit Strings to `CreateArrayFromList` (`"ab".split("")`).
12. **43** `AllocateSharedArrayBuffer` step 9.c passes a Shared Data Block to `SetValueInBuffer`.
13. **61 & 62** Annex B.1.2.5 `CompileSubpattern` calls non-existent 2-arg `CompileAtom` on `QuantifiableAssertion` (`/(?=a)*/`), and `CountLeftCapturingParensWithin` step 1 asserts `#sec-patterns`.
14. **59 & 11** `RegExpBuiltinExec` step 13.b out-of-bounds `element _lastIndex_ of _string_` at `_lastIndex_ = _length_`, and surrogate-pair `lastIndex` mismatch (#128, #2511).
15. **66** `GetExportedNames` 3.a and `ResolveExport` 3.a.i assert circularity on acyclic diamond `export *` module DAGs.
16. **67, 23, 48, 50** §29 Memory Model: unequal overlapping RMW cycle non-termination in `ValueOfReadEvent`, unquantified `reads-bytes-from` in §29.7.5, `Races` vacuous `"not both"`, `~init~` equal-range `happens-before`, and block-less memory ranges.
17. **35, 39, 46, 58, 64** Cover-grammar defects: `Contains |AwaitExpression|`, failed-cover rule ordering, covered-node parent (`IsInTailPosition`), virtual `;` inside covers, and supplemental `"covered by"`.
18. **55, 40, 41, 44, 26, 49, 63** Grammar & Annex B defects: `RegExpUnicodeEscapeSequence` lookahead, Annex B RegExp ordering/group-count self-reference (#2445), first-line `-->`, lookahead past virtual `;`, Annex B modifier early errors, `IsCharacterClass` on `\c1`, and B.3.2/B.3.3 type & synthetic-block gaps.
19. **02, 05, 09, 10, 12, 13, 14, 15, 29, 31, 32, 36, 38, 45, 65, 68** Remaining algorithm, assertion, and sort defects.

## Proposed normative changes (file separately)
- **21** `<ZWNJ>` / `<ZWJ>` non-Unicode `IdentityEscape` after Unicode 15.1.
- **51 & 54** Implementation-defined maximum `BigInt` size and sub-`2^53 - 1` maximum `String` length throwing *RangeError*.
