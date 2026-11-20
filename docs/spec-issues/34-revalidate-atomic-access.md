# 34. RevalidateAtomicAccess checks only the element's first byte, and the buffer operation's Assert fails

The pinned text no longer has this defect: RevalidateAtomicAccess now checks the element's last byte, and the model's
erratum `RevalidateAtomicAccess` is retired.

- **Location:** §25.4.3.4 RevalidateAtomicAccess (`#sec-revalidateatomicaccess`), steps 4–6 (step 4 before the
  fix), reached from §25.4.13 Atomics.store (`#sec-atomics.store`), §25.4.9 Atomics.load (`#sec-atomics.load`) and
  §25.4.3.17 AtomicReadModifyWrite (`#sec-atomicreadmodifywrite`), with step 2 of §25.1.3.18 SetValueInBuffer
  (`#sec-setvalueinbuffer`), §25.1.3.16 GetValueFromBuffer (`#sec-getvaluefrombuffer`) and §25.1.3.19
  GetModifySetValueInBuffer (`#sec-getmodifysetvalueinbuffer`).
- **Kind:** failing Assert (fixed in the pinned text).
- **Model erratum:** none now: `RevalidateAtomicAccess` is retired, and the model runs the pinned text as written.
  Its literal reading stopped at step 2 of SetValueInBuffer (from Atomics.store), GetModifySetValueInBuffer (from
  AtomicReadModifyWrite) and GetValueFromBuffer (from Atomics.load); its proposed reading checked the whole element,
  as the pinned text does.
- **Upstream:** Checked 2026-11-19: fixed. Issue #3924 (closed, 2026-10), "RevalidateAtomicAccess only bounds-checks
  the element's first byte, permitting an OOB atomic access", reported it; PR #3926, "Normative: Update
  RevalidateAtomicAccess to account for all bytes of a TypedArray element", merged 2026-10-09 as commit 5e0f8b33b.
  test262 PR #5106 (open, 2026-08), "Atomics: Test RevalidateAtomicAccess with barely-too-short ArrayBuffers", adds
  tests and is not merged.

## Text

RevalidateAtomicAccess, in the pinned text:

> 2. Let _taRecord_ be ? ValidateTypedArrayBounds(_ta_, ~unordered~).
> 3. Assert: _byteIndexInBuffer_ ≥ _ta_.[[ByteOffset]].
> 4. Let _elementSize_ be TypedArrayElementSize(_ta_).
> 5. Let _elementLastByteIndex_ be _byteIndexInBuffer_ + _elementSize_ - 1.
> 6. If _elementLastByteIndex_ ≥ _taRecord_.[[CachedBufferByteLength]], throw a *RangeError* exception.
> 7. Return ~unused~.

Steps 4–6 replace this step 4 of the text before the fix (steps 1–3 were as now):

<!-- quote: ECMA-262 before the fix -->

> 4. If _byteIndexInBuffer_ ≥ _taRecord_.[[CachedBufferByteLength]], throw a *RangeError* exception.

The operation's description: "This operation revalidates the index within the backing buffer for atomic operations
after all argument coercions are performed in Atomics methods, as argument coercions can have arbitrary side effects,
which could cause the buffer to become out of bounds."

SetValueInBuffer, GetValueFromBuffer and GetModifySetValueInBuffer, step 2:

> 2. Assert: There are sufficient bytes in _arrayBuffer_ starting at _byteIndex_ to represent a value of _type_.

## Problem

A coercion of the value or index argument can shrink a resizable ArrayBuffer. The old step 4 threw only when the
element's first byte was outside the buffer. If the new length falls inside the element (_byteIndexInBuffer_ <
length < _byteIndexInBuffer_ + TypedArrayElementSize(_ta_)), the operation returned normally, and the buffer operation
that follows failed its Assert. A length-tracking TypedArray reaches this: it stays in bounds (ValidateTypedArrayBounds
succeeds) while its last element is cut. Atomics.compareExchange does not fail an Assert: it binds _block_ before the
coercions (step 3) and, under the old step 4, compared and stored into the old Data Block.

## Examples

[examples/34-revalidate-atomic-access.js](examples/34-revalidate-atomic-access.js) (outputs:
[RESULTS.md](examples/RESULTS.md#34-revalidate-atomic-accessjs)): a length-tracking `Int32Array` over a 16-byte
resizable buffer; the coercion resizes it to 6 bytes; the index is 1 (byte index 4, bytes 4–7, only 4–5 left).

```js
function test(name, f) {
  var rab = new ArrayBuffer(16, { maxByteLength: 16 });
  var ta = new Int32Array(rab);
  var shrink = { valueOf() { rab.resize(6); return 1; } };
  try { print(name + ": returned " + f(ta, shrink)); }
  catch (e) { print(name + ": " + e.constructor.name); }
}
test("Atomics.store", (ta, s) => Atomics.store(ta, 1, s));
test("Atomics.add", (ta, s) => Atomics.add(ta, 1, s));
test("Atomics.load", (ta, s) => Atomics.load(ta, s));
test("Atomics.compareExchange", (ta, s) => Atomics.compareExchange(ta, 1, 0, s));
```

| | `store` | `add` | `load` | `compareExchange` |
|---|---|---|---|---|
| text before the fix | SetValueInBuffer 2 fails | GetModifySetValueInBuffer 2 fails | GetValueFromBuffer 2 fails | `returned 0` (the old block) |
| pinned text | `RangeError` | `RangeError` | `RangeError` | `RangeError` |
| SpiderMonkey | `RangeError` | `RangeError` | `RangeError` | `RangeError` |
| V8, JavaScriptCore | `TypeError` | `TypeError` | `TypeError` | `TypeError` |
| formal model | `RangeError` | `RangeError` | `RangeError` | `RangeError` |

All three engines reject the access; V8 and JavaScriptCore throw a *TypeError* where the pinned text throws a
*RangeError*.

## The fix

The pinned text against the text before it:

```diff
--- a/spec.html
+++ b/spec.html
@@
           1. NOTE: Bounds checking is not a synchronizing operation when _ta_'s backing buffer is a growable SharedArrayBuffer.
           1. Let _taRecord_ be ? ValidateTypedArrayBounds(_ta_, ~unordered~).
           1. Assert: _byteIndexInBuffer_ ≥ _ta_.[[ByteOffset]].
-          1. If _byteIndexInBuffer_ ≥ _taRecord_.[[CachedBufferByteLength]], throw a *RangeError* exception.
+          1. Let _elementSize_ be TypedArrayElementSize(_ta_).
+          1. Let _elementLastByteIndex_ be _byteIndexInBuffer_ + _elementSize_ - 1.
+          1. If _elementLastByteIndex_ ≥ _taRecord_.[[CachedBufferByteLength]], throw a *RangeError* exception.
           1. Return ~unused~.
         </emu-alg>
       </emu-clause>
```

## test262

None in the pinned test262 separates the two texts: a test that shrinks the buffer past the element's first byte is
rejected by the old step 4 as well, so only a cut inside the element does. One in the shape of the example:

```js
var rab = new ArrayBuffer(16, { maxByteLength: 16 });
var ta = new Int32Array(rab);
assert.throws(RangeError, function() {
  Atomics.store(ta, 1, { valueOf() { rab.resize(6); return 1; } });
});
```

V8 and JavaScriptCore would fail it (a *TypeError*).
