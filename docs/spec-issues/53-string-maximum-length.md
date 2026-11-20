# 53. Maximum String length is unspecified and leaves `"a".repeat(2 ** 30)` exact up to `2^53 - 1`

- **Location:** §6.1.4 The String Type (`#sec-ecmascript-language-types-string-type`), first paragraph; §22.1.3.16
  `String.prototype.repeat` (`#sec-string.prototype.repeat`), step 7; §22.1.3.15.1 StringPaddingBuiltinsImpl
  (`#sec-stringpaddingbuiltinsimpl`), step 7; §22.1.3.5 `String.prototype.concat` (`#sec-string.prototype.concat`),
  step 5.b; §13.15.3 ApplyStringOrNumericBinaryOperator (`#sec-applystringornumericbinaryoperator`), step 1.c.iii;
  §23.1.3.18.1 JoinIndexedProperties (`#sec-joinindexedproperties`), steps 4.a and 4.d.iii.
- **Kind:** missing limit (engines throw a *RangeError* past their smaller maximum String lengths).
- **Model erratum:** `StringMaximumLength`, default reading proposed; its readings: literal, proposed. The proposed
  reading asks the host (`StringTooLarge`, `spec/formal/strings.emu`) before constructing the String whether its
  length exceeds the implementation's maximum (the model's host answers *true* past 2<sup>28</sup> = 268,435,456 code
  units) and throws a *RangeError* if so; the literal reading attempts the result up to 2<sup>53</sup> - 1 code units.
- **Upstream:** Checked 2026-11-20: none found that specifies a maximum String length throw (searched for String with
  "maximum length" and "RangeError"). Related: issue #4063 (closed, 2026-10, as not planned), "Specify that exceeding
  resource limits may throw".

## Text

§6.1.4:

> The String type is the set of all ordered sequences of zero or more 16-bit unsigned integer values (“elements”) up to a maximum length of 2<sup>53</sup> - 1 elements.

`String.prototype.repeat`:

> 7. Return the String value that is made from _n_ copies of _string_ appended together.

`StringPaddingBuiltinsImpl`:

> 7. Return StringPad(_string_, _intMaxLength_, _fillString_, _placement_).

`String.prototype.concat`:

> b. Set _result_ to the string-concatenation of _result_ and _nextString_.

`ApplyStringOrNumericBinaryOperator`:

> iii. Return the string-concatenation of _leftString_ and _rightString_.

`JoinIndexedProperties`:

> a. If _k_ > 0, set _result_ to the string-concatenation of _result_ and _separator_.

> iii. Set _result_ to the string-concatenation of _result_ and _elementString_.

## Problem

While §6.1.4 permits Strings up to length 2<sup>53</sup> - 1, no runtime has 18 petabytes for one UTF-16 String. In
practice engines enforce a much smaller maximum length and throw a *RangeError* when an operation would exceed it
(V8 2<sup>28</sup> on 32-bit targets and 2<sup>29</sup> - 24 on 64-bit, SpiderMonkey 2<sup>30</sup> - 2,
JavaScriptCore 2<sup>31</sup> - 1). Read literally, `"a".repeat(2 ** 30)` and `"a".padStart(2 ** 30, "b")` must
succeed (or hit an unspecified out-of-memory failure rather than catching a *RangeError*), whereas
`"a".padStart(2 ** 32, "")` returns `"a"` because StringPad returns early when `_fillString_` is empty.

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
| V8 (Node.js) | `RangeError` | `0` | `RangeError` | `"a"` |
| SpiderMonkey (js140) | `RangeError` | `0` | `RangeError` | `"a"` |
| JavaScriptCore (Bun) | allocates 2 GB or throws `RangeError` | `0` | allocates or throws `RangeError` | `"a"` |
| formal model (proposed reading) | `repeat: RangeError` | `0` | `padStart: RangeError` | `"a"` |

## Proposed wording

Allow an implementation-defined maximum String length at most 2<sup>53</sup> - 1, checked before constructing Strings
that grow past it (after checking non-empty `_fillString_` in StringPaddingBuiltinsImpl), throwing a *RangeError*
exception.

## test262

Existing tests verify edge cases around `repeat(Infinity)` / `repeat(-1)` throwing *RangeError* and large `padStart`
counts with an empty fill string (`""`) returning the original string. Under `--reading proposed`, engines throwing
*RangeError* past `maxStringLength` match V8/SpiderMonkey.
