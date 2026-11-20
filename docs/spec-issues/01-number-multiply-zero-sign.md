# 01. Number::multiply gives +0 for `+0 × -5`

- **Location:** §6.1.6.1.4 Number::multiply (`#sec-numeric-types-number-multiply`), step 6, and the clause's
  description.
- **Kind:** contradiction (a step's result against the clause's description).
- **Model erratum:** `NumberMultiplyZeroSign`, default reading proposed; its readings: literal, proposed. The
  proposed reading returns *-0*𝔽 when one operand is *+0*𝔽 and the other is negative.
- **Upstream:** Checked 2026-11-19: PR #4072 (open, 2026-11), "Normative: Fix the sign of zero results in
  Number::multiply", proposes a fix for this case (its description names `0 * -5` and `-5 * 0`); no issue was found
  (searched tc39/ecma262's issues and pull requests for "Number::multiply"). PR #2700 (merged 2022-03, commit
  4ef927684) added the steps for *-0*𝔽 operands and left this case.

## Text

The clause's description:

> It performs multiplication according to the rules of IEEE 754-2019 binary double-precision arithmetic,
> producing the product of _x_ and _y_.

The last steps:

> 4. If _x_ is *-0*𝔽, then …
> 5. If _y_ is *-0*𝔽, then …
> 6. Return 𝔽(ℝ(_x_) × ℝ(_y_)).

and §6.1.6.1's definition of 𝔽(_x_): "… if *+0*𝔽 was chosen, replace it with *-0*𝔽 if and only if _x_ < 0; …".

## Problem

For _x_ = *+0*𝔽 and _y_ = -5𝔽, steps 1–5 do not apply. Step 6 computes ℝ(_x_) × ℝ(_y_) = 0, a mathematical
value with no sign, and 𝔽(0) is *+0*𝔽. IEEE 754-2019 §6.3 makes the sign of a product the exclusive or of the
operands' signs, so the description gives *-0*𝔽. The two disagree exactly when one operand is *+0*𝔽 and the other
is finite and negative. A product that only rounds to zero is not affected: 𝔽 of a negative real is *-0*𝔽.

## Examples

[examples/01-number-multiply-zero-sign.js](examples/01-number-multiply-zero-sign.js) (outputs:
[RESULTS.md](examples/RESULTS.md#01-number-multiply-zero-signjs)):

```js
print(String(1 / (0 * -5)));   // +0 × -5
print(String(1 / (-5 * 0)));   // -5 × +0
print(String(1 / (0 * 5)));    // +0 × 5
print(String(Object.is(-5 * 0, -0)));
```

| | `1/(0*-5)` | `1/(-5*0)` | `1/(0*5)` | `Object.is(-5*0, -0)` |
|---|---|---|---|---|
| literal step 6 | `Infinity` | `Infinity` | `Infinity` | `false` |
| V8, SpiderMonkey, JavaScriptCore | `-Infinity` | `-Infinity` | `Infinity` | `true` |
| formal model, literal reading | `Infinity` | `Infinity` | `Infinity` | `false` |
| formal model, proposed reading (default) | `-Infinity` | `-Infinity` | `Infinity` | `true` |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -1817,6 +1817,9 @@
             1. If _y_ is *-0*<sub>𝔽</sub>, then
               1. If _x_ &lt; *-0*<sub>𝔽</sub>, return *+0*<sub>𝔽</sub>.
               1. Return *-0*<sub>𝔽</sub>.
+            1. If _x_ is *+0*<sub>𝔽</sub> or _y_ is *+0*<sub>𝔽</sub>, then
+              1. If _x_ &lt; *-0*<sub>𝔽</sub> or _y_ &lt; *-0*<sub>𝔽</sub>, return *-0*<sub>𝔽</sub>.
+              1. Return *+0*<sub>𝔽</sub>.
             1. Return 𝔽(ℝ(_x_) × ℝ(_y_)).
           </emu-alg>
           <emu-note>
```

## test262

`language/expressions/multiplication/S11.5.1_A4_T2.js` tests the sign of a product. Its description states the
IEEE rule ("negative if the operands have different signs"), but its assertions cover only products of ±1
(`1 * -1`, …) and products of two signed zeros (`0 * -0`, `-0 * 0`, …), not a zero times a nonzero finite Number
such as `0 * -5`. No test in test262 multiplies *+0*𝔽 by a negative finite Number, so none fails under the literal
text.
