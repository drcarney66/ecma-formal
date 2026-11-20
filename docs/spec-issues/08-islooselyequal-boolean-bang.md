# 08. `Object.create(null) == false`: IsLooselyEqual asserts that ToPrimitive succeeds

The pinned text no longer has this defect: steps 9 and 10 now return `?` IsLooselyEqual(…), and the model's erratum
`IsLooselyEqualBooleanAbrupt` is retired.

- **Location:** §7.2.13 IsLooselyEqual (`#sec-islooselyequal`), steps 9 and 10; §13.11.1 Runtime Semantics:
  Evaluation (`#sec-equality-operators-runtime-semantics-evaluation`), step 5.
- **Kind:** failing `!` (fixed).
- **Model erratum:** none: `IsLooselyEqualBooleanAbrupt` is retired, and the model runs the pinned text as written.
  Its literal reading stopped a run at steps 9 and 10; its proposed reading was the text that is now pinned.
- **Upstream:** Checked 2026-11-19: fixed. Issue #4066 (closed, 2026-11), "Incorrect `!` assertion on recursive
  `IsLooselyEqual` calls in steps 9–10", reported it; PR #4067, "Editorial: Fix incorrect ! in IsLooselyEqual", merged
  2026-11-08 as commit 8a3e4aae7, replaced the outer `!` of steps 9 and 10 by `?`.

## Text

As pinned:

> 9. If _x_ is a Boolean, return ? IsLooselyEqual(! ToNumber(_x_), _y_).
> 10. If _y_ is a Boolean, return ? IsLooselyEqual(_x_, ! ToNumber(_y_)).
> 11. If _x_ is either a String, a Number, a BigInt, or a Symbol and _y_ is an Object, return ! IsLooselyEqual(_x_,
>     ? ToPrimitive(_y_)).
> 12. If _x_ is an Object and _y_ is either a String, a Number, a BigInt, or a Symbol, return ! IsLooselyEqual(?
>     ToPrimitive(_x_), _y_).

Before the fix, steps 9 and 10 read:

<!-- quote: ECMA-262 before the fix -->
> 9. If _x_ is a Boolean, return ! IsLooselyEqual(! ToNumber(_x_), _y_).
> 10. If _y_ is a Boolean, return ! IsLooselyEqual(_x_, ! ToNumber(_y_)).

## Problem

Before the fix, when _x_ is a Boolean and _y_ an Object, step 9 called IsLooselyEqual(_n_, _y_) with a Number _n_.
That call reaches step 11, whose `? ToPrimitive(_y_)` throws when _y_ has no callable `valueOf` or `toString`
(OrdinaryToPrimitive step 4) or when one of them throws. The `!` of step 9 asserted that the call completes
normally, and it does not. Step 10 was the same with the operands exchanged. The other `!` of the algorithm,
unchanged, are sound: their operands are primitives.

The equality operators evaluate IsLooselyEqual(_rightValue_, _leftValue_) (§13.11.1), so `x == false` reaches
step 9 and `false == x` step 10.

## Examples

[examples/08-islooselyequal-boolean-bang.js](examples/08-islooselyequal-boolean-bang.js) (outputs:
[RESULTS.md](examples/RESULTS.md#08-islooselyequal-boolean-bangjs)):

```js
var dict = Object.create(null);
try { print(dict == false); } catch (e) { print("dict == false: " + e.constructor.name); }
try { print(true == { valueOf() { throw new RangeError("v"); } }); }
catch (e) { print("true == {valueOf throws}: " + e.constructor.name); }
try { print(1 == dict); } catch (e) { print("1 == dict: " + e.constructor.name); }
```

| | `dict == false` | `true == {valueOf throws}` | `1 == dict` |
|---|---|---|---|
| the text before the fix | step 9's `!` fails | step 10's `!` fails | *TypeError* |
| the pinned text | *TypeError* | *RangeError* | *TypeError* |
| V8, SpiderMonkey, JavaScriptCore | `TypeError` | `RangeError` | `TypeError` |
| formal model (the pinned text) | `TypeError` | `RangeError` | `TypeError` |

## test262

No test in `language/expressions/equals/` or `language/expressions/does-not-equals/` compares a Boolean with an
Object whose ToPrimitive throws. `language/expressions/equals/S11.9.1_A7.9.js`
compares `true` with objects whose `valueOf` succeeds, and `coerce-symbol-to-prim-err.js` compares an object whose
@@toPrimitive throws with `0`.
