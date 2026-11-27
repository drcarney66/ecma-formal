# 54. Maximum String length below `2^53 - 1`: `"a".repeat(2 ** 30)` throws a *RangeError* past host memory limits

- **Location:** §6.1.4 The String Type (`#sec-ecmascript-language-types-string-type`), first paragraph; §22.1.3.18
  `String.prototype.repeat` (`#sec-string.prototype.repeat`), step 7; §22.1.3.17.1 StringPaddingBuiltinsImpl
  (`#sec-stringpaddingbuiltinsimpl`), step 7; §22.1.3.5 `String.prototype.concat` (`#sec-string.prototype.concat`),
  step 5.b; §13.15.3 ApplyStringOrNumericBinaryOperator (`#sec-applystringornumericbinaryoperator`), step 1.c.iii;
  §23.1.3.18.1 JoinIndexedProperties (`#sec-joinindexedproperties`), steps 4.a and 4.d.iii.
- **Kind:** proposed normative change (a finite-hardware resource limit analogous to [51](51-bigint-maximum-size.md); for
  the missing `> 2^53 - 1` check in `repeat`, `concat`, `+` and `JoinIndexedProperties`, see
  [53](53-string-length-overflow.md)).
- **Model erratum:** `StringMaximumLength`, baked-in SpecTec reading proposed (`$StringTooLarge` in
  `spec/spectec/clauses/S13.spectec`, `S22.spectec`, `S23.spectec`). SpecTec queries the host (`StringTooLarge`,
  answering *true* past 2<sup>28</sup> = 268,435,456 code units in `lean/Engine/Host/Core.lean`) before constructing the
  String and throws a *RangeError* if so; the literal text requires forming every String up to 2<sup>53</sup> - 1 code
  units.
- **Upstream:** Checked 2026-11-20: none found that specifies an implementation-defined sub-`2^53 - 1` maximum String
  length throw (searched for String with "maximum length" and "RangeError"). Related: issue #4063 (closed, 2026-10),
  "Specify that exceeding resource limits may throw".

## Text

§6.1.4:

> The String type is the set of all ordered sequences of zero or more 16-bit unsigned integer values (“elements”) up to a maximum length of 2<sup>53</sup> - 1 elements.

`String.prototype.repeat`:

> 7. Return the String value that is made from _n_ copies of _string_ appended together.

`StringPaddingBuiltinsImpl`:

> 7. Return StringPad(_string_, _intMaxLength_, _fillString_, _placement_).

## Problem

While §6.1.4 permits Strings up to length 2<sup>53</sup> - 1, no runtime has 18 petabytes for one UTF-16 String. Every
engine enforces a smaller implementation-defined maximum String length and throws a *RangeError* when an operation would
exceed it (V8 2<sup>28</sup> on 32-bit targets and 2<sup>29</sup> - 24 on 64-bit, SpiderMonkey 2<sup>30</sup> - 2,
JavaScriptCore 2<sup>31</sup> - 1). Read literally, `"a".repeat(2 ** 30)` and `"a".padStart(2 ** 30, "b")` must return
1-billion-element Strings, whereas `"a".padStart(2 ** 32, "")` returns `"a"` because `StringPad` returns early when
`_fillString_` is empty.

## Examples

```js
try { "a".repeat(2 ** 30); } catch (e) { print("repeat: " + e.constructor.name); }
print('"" repeat:', "".repeat(2 ** 40).length);
try { "a".padStart(2 ** 30, "b"); } catch (e) { print("padStart: " + e.constructor.name); }
print("empty fill:", "a".padStart(2 ** 32, ""));
```

| | `"a".repeat(2 ** 30)` | `"".repeat(2 ** 40).length` | `"a".padStart(2 ** 30, "b")` | `"a".padStart(2 ** 32, "")` |
|---|---|---|---|---|
| literal text | 2<sup>30</sup>-length String | `0` | 2<sup>30</sup>-length String | `"a"` |
| V8, SpiderMonkey, JavaScriptCore | `RangeError` | `0` | `RangeError` | `"a"` |
| formal model (proposed reading) | `repeat: RangeError` | `0` | `padStart: RangeError` | `"a"` |

## Proposed wording

Allow an implementation-defined maximum String length at most 2<sup>53</sup> - 1, checked before constructing Strings
that grow past it (after checking non-empty `_fillString_` in `StringPaddingBuiltinsImpl`), throwing a *RangeError*
exception.

## test262

Existing tests check `repeat(-1)` / `repeat(Infinity)` throwing *RangeError* and large `padStart` counts with an empty
fill string (`""`) returning the original String; none requires constructing a `2^30`-unit String.
