# 28. ToBigInt: the Boolean row writes its results as source-text literals and its cases as one sentence

- **Location:** §7.1.15 ToBigInt (`#sec-tobigint`), the BigInt Conversions table (`#table-tobigint`), the Boolean row.
- **Kind:** editorial (notation).
- **Model erratum:** none: the model reads `` `1n` `` as a BigInt literal and the sentence as a value by two cases, so
  the change below alters no result.
- **Upstream:** Checked 2026-11-19: none found (searched for "ToBigInt" with Boolean).

## Text

> | Boolean | Return `1n` if _primitive_ is *true* and `0n` if _primitive_ is *false*. |

## Why it is irregular

- **The literals.** `1n` and `0n` are ECMAScript source text (BigInt literals in code font). Nowhere else does the specification write a BigInt value this way; it writes *1*<sub>ℤ</sub> and *0*<sub>ℤ</sub> (the BigInt type's notation), as in BigInt::unaryMinus, BigInt::exponentiate and the other BigInt operations. A reader has to evaluate source text to get the value.
- **The cases.** The cell is the only step in the specification of the form "Return _a_ if _c_ and _b_ if _d_". The other conversion tables, and the algorithms, write two cases as an If step and a Return step.

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -5260,6 +5260,6 @@
               Boolean
             </td>
             <td>
-              Return `1n` if _primitive_ is *true* and `0n` if _primitive_ is *false*.
+              If _primitive_ is *true*, return *1*<sub>ℤ</sub>. Otherwise, return *0*<sub>ℤ</sub>.
             </td>
           </tr>
```

or, in the table's one-sentence style: "Return *1*<sub>ℤ</sub> if _primitive_ is *true*; otherwise return *0*<sub>ℤ</sub>."
