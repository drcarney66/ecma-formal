# 31. Sort: a comparator that returns ±∞ is neither consistent nor inconsistent

- **Location:** §23.1.3.30.1 SortIndexedProperties (`#sec-sortindexedproperties`), the sort order conditions and the
  definition of a consistent comparator after its algorithm, with §23.1.3.30.2 CompareArrayElements
  (`#sec-comparearrayelements`), step 4.a, §23.2.4.8 CompareTypedArrayElements (`#sec-comparetypedarrayelements`),
  step 2.a, and §5.2.6 Mathematical Operations (`#sec-mathematical-operations`).
- **Kind:** an undefined value (ℝ of a non-finite Number) in a definition.
- **Model erratum:** `SortInfiniteComparator`, default reading test262; its readings: literal, test262, proposed.
  Read literally, a ±∞ result stops the run (ℝ has no value); the test262 and proposed readings take no ℝ, so the
  order is the host's, and the model's hosts order by the sign of the result.
- **Upstream:** Checked 2026-11-19: none found (searched for "consistent comparator" and for comparator with
  Infinity). Issue #3172 (open, 2023-09), "Call SortCompare only on actual elements", is about which values
  SortCompare is called on.

## Text

The definition of a consistent comparator:

> The notation _a_ &lt;<sub>C</sub> _b_ means ℝ(_comparator_(_a_, _b_)) &lt; 0; _a_ =<sub>C</sub> _b_ means
> ℝ(_comparator_(_a_, _b_)) = 0; and _a_ &gt;<sub>C</sub> _b_ means ℝ(_comparator_(_a_, _b_)) &gt; 0.
>
> - Calling _comparator_(_a_, _b_) always returns the same value _v_ when given a specific pair of values _a_ and _b_
>   as its two arguments. Furthermore, _v_ is a Number, and _v_ is not *NaN*. Note that this implies that exactly one
>   of _a_ &lt;<sub>C</sub> _b_, _a_ =<sub>C</sub> _b_, and _a_ &gt;<sub>C</sub> _b_ will be true for a given pair of
>   _a_ and _b_.

The sort order conditions: "if ℝ(_sortCompare_(old[_j_], old[_k_])) &lt; 0, then π(_j_) &lt; π(_k_)" and "if
ℝ(_sortCompare_(old[_j_], old[_k_])) = 0, then π(_j_) &lt; π(_k_)". CompareArrayElements 4.a–4.c:

> a. Let _result_ be ? ToNumber(? Call(_comparator_, *undefined*, « _x_, _y_ »)).
> b. If _result_ is *NaN*, return *+0*<sub>𝔽</sub>.
> c. Return _result_.

§5.2.6: "The mathematical value of non-finite values is not defined."

## Problem

A user comparator's result reaches the definition through ToNumber, with only *NaN* mapped to *+0*<sub>𝔽</sub>, so
*+∞*<sub>𝔽</sub> and *-∞*<sub>𝔽</sub> reach it. For them ℝ is not defined, so none of &lt;<sub>C</sub>,
=<sub>C</sub>, &gt;<sub>C</sub> has a value, and the "Note that this implies" sentence is false: the result is a
Number and not *NaN*, yet the trichotomy fails. Whether `(a, b) => a < b ? -Infinity : a > b ? Infinity : 0` is a
consistent comparator, and so whether the sort order is fixed or implementation-defined, is not decided by the text;
the two sort order conditions have the same gap. Every engine orders by the sign, as for finite results. Comparing
the Number with *+0*<sub>𝔽</sub> (§5.2.6: on Numbers, the operators are IEEE 754-2019's, so *-0*<sub>𝔽</sub> =
*+0*<sub>𝔽</sub>) gives every non-*NaN* Number a value and changes nothing for finite results.

## Examples

[examples/31-sort-infinite-comparator.js](examples/31-sort-infinite-comparator.js) (outputs:
[RESULTS.md](examples/RESULTS.md#31-sort-infinite-comparatorjs)):

```js
print([3, 1, 2].sort((a, b) => a < b ? -Infinity : a > b ? Infinity : 0).join());
print([5, 3, 4, 1, 2].sort((a, b) => (a - b) * Infinity).join());
print(["b", "a", "c"].sort((a, b) => a < b ? -Infinity : a > b ? Infinity : 0).join());
```

| | output |
|---|---|
| literal text | undecided: any permutation if the comparator is not consistent, `1,2,3`, `1,2,3,4,5`, `a,b,c` if it is |
| proposed text | `1,2,3`, `1,2,3,4,5`, `a,b,c` |
| V8, SpiderMonkey, JavaScriptCore | `1,2,3`, `1,2,3,4,5`, `a,b,c` |
| formal model, literal reading | none: the run stops at the first ±∞ result |
| formal model, test262 and proposed readings | `1,2,3`, `1,2,3,4,5`, `a,b,c` |

## Proposed wording

```diff
--- a/spec.html
+++ b/spec.html
@@ -41343,14 +41343,14 @@
               There must be some mathematical permutation π of the non-negative integers less than _itemCount_, such that for every non-negative integer _j_ less than _itemCount_, the element <emu-eqn>old[_j_]</emu-eqn> is exactly the same as <emu-eqn>new[π(_j_)]</emu-eqn>.
             </li>
             <li>
-              Then for all non-negative integers _j_ and _k_, each less than _itemCount_, if <emu-eqn>ℝ(_sortCompare_(old[_j_], old[_k_])) &lt; 0</emu-eqn>, then <emu-eqn>π(_j_) &lt; π(_k_)</emu-eqn>.
+              Then for all non-negative integers _j_ and _k_, each less than _itemCount_, if <emu-eqn>_sortCompare_(old[_j_], old[_k_]) &lt; *+0*<sub>𝔽</sub></emu-eqn>, then <emu-eqn>π(_j_) &lt; π(_k_)</emu-eqn>.
             </li>
             <li>
-              And for all non-negative integers _j_ and _k_ such that _j_ &lt; _k_ &lt; _itemCount_, if <emu-eqn>ℝ(_sortCompare_(old[_j_], old[_k_])) = 0</emu-eqn>, then <emu-eqn>π(_j_) &lt; π(_k_)</emu-eqn>; i.e., the sort is stable.
+              And for all non-negative integers _j_ and _k_ such that _j_ &lt; _k_ &lt; _itemCount_, if <emu-eqn>_sortCompare_(old[_j_], old[_k_]) = *+0*<sub>𝔽</sub></emu-eqn>, then <emu-eqn>π(_j_) &lt; π(_k_)</emu-eqn>; i.e., the sort is stable.
             </li>
           </ul>
           <p>Here the notation <emu-eqn>old[_j_]</emu-eqn> is used to refer to <emu-eqn>_items_[_j_]</emu-eqn> before step <emu-xref href="#step-array-sort"></emu-xref> is executed, and the notation <emu-eqn>new[_j_]</emu-eqn> to refer to <emu-eqn>_items_[_j_]</emu-eqn> after step <emu-xref href="#step-array-sort"></emu-xref> has been executed.</p>
-          <p>An Abstract Closure or function _comparator_ is a <dfn id="consistent-comparator">consistent comparator</dfn> for a set of values _values_ if all of the requirements below are met for all values _a_, _b_, and _c_ (possibly the same value) in the set _values_: The notation <emu-eqn>_a_ &lt;<sub>C</sub> _b_</emu-eqn> means <emu-eqn>ℝ(_comparator_(_a_, _b_)) &lt; 0</emu-eqn>; <emu-eqn>_a_ =<sub>C</sub> _b_</emu-eqn> means <emu-eqn>ℝ(_comparator_(_a_, _b_)) = 0</emu-eqn>; and <emu-eqn>_a_ ><sub>C</sub> _b_</emu-eqn> means <emu-eqn>ℝ(_comparator_(_a_, _b_)) > 0</emu-eqn>.</p>
+          <p>An Abstract Closure or function _comparator_ is a <dfn id="consistent-comparator">consistent comparator</dfn> for a set of values _values_ if all of the requirements below are met for all values _a_, _b_, and _c_ (possibly the same value) in the set _values_: The notation <emu-eqn>_a_ &lt;<sub>C</sub> _b_</emu-eqn> means <emu-eqn>_comparator_(_a_, _b_) &lt; *+0*<sub>𝔽</sub></emu-eqn>; <emu-eqn>_a_ =<sub>C</sub> _b_</emu-eqn> means <emu-eqn>_comparator_(_a_, _b_) = *+0*<sub>𝔽</sub></emu-eqn>; and <emu-eqn>_a_ ><sub>C</sub> _b_</emu-eqn> means <emu-eqn>_comparator_(_a_, _b_) > *+0*<sub>𝔽</sub></emu-eqn>.</p>
           <ul>
             <li>
               Calling _comparator_(_a_, _b_) always returns the same value _v_ when given a specific pair of values _a_ and _b_ as its two arguments. Furthermore, _v_ is a Number, and _v_ is not *NaN*. Note that this implies that exactly one of _a_ &lt;<sub>C</sub> _b_, _a_ =<sub>C</sub> _b_, and _a_ ><sub>C</sub> _b_ will be true for a given pair of _a_ and _b_.
```

## test262

None found: the sort tests use ±∞ as elements, not as comparator results. A test that sorts with the first comparator
above and expects `1,2,3` passes on every engine tried and holds only under the proposed text.
