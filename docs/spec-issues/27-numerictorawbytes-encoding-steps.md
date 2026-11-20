# 27. NumericToRawBytes: the encoding steps put their byte order and NaN latitude in extra sentences

- **Location:** §25.1.3.17 NumericToRawBytes (`#sec-numerictorawbytes`), steps 1.a, 2.a, 3.a, 4.d.i and 4.e.i.
- **Kind:** editorial (irregular steps), with one wording question.
- **Model erratum:** none: the model reads the steps whole; the NaN latitude is the host choice NaNEncoding
  (register row `nan-encoding`, `spec/formal/decisions.md`).
- **Upstream:** Checked 2026-11-19: issue #3567 (open, 2025-04), "Remove language about choosing same encoding for
  NaNs in NumericToRawBytes", asks to remove the NaN sentences, one part of this; no pull request was found.

## Text

> 1. If _type_ is ~float16~, then
>    a. Let _rawBytes_ be a List whose elements are the 2 bytes that are the result of converting _value_ to IEEE
>       754-2019 binary16 format using roundTiesToEven mode. The bytes are arranged in little endian order. If
>       _value_ is *NaN*, _rawBytes_ may be set to any implementation chosen IEEE 754-2019 binary16 format NaN
>       encoding. An implementation must always choose the same encoding for each implementation distinguishable
>       *NaN* value.

> 4. Else,
>    …
>    d. If _intValue_ ≥ 0, then
>       i. Let _rawBytes_ be a List whose elements are the _n_-byte binary encoding of _intValue_. The bytes are
>          ordered in little endian order.
>    e. Else,
>       i. Let _rawBytes_ be a List whose elements are the _n_-byte binary two's complement encoding of _intValue_.
>          The bytes are ordered in little endian order.

Step 2.a repeats 1.a for binary32. Step 3.a has the same sentences of order and NaN latitude after a first sentence
without a conversion:

> 3. Else if _type_ is ~float64~, then
>    a. Let _rawBytes_ be a List whose elements are the 8 bytes that are the IEEE 754-2019 binary64 format encoding of
>       _value_. The bytes are arranged in little endian order. If _value_ is *NaN*, _rawBytes_ may be set to any
>       implementation chosen IEEE 754-2019 binary64 format NaN encoding. An implementation must always choose the
>       same encoding for each implementation distinguishable *NaN* value.

RawBytesToNumeric (§25.1.3.14, `#sec-rawbytestonumeric`), the inverse:

> 3. If _type_ is ~float16~, then
>    a. Let _value_ be the byte elements of _rawBytes_ concatenated and interpreted as a little-endian bit string
>       encoding of an IEEE 754-2019 binary16 value.

## Why it is irregular

Each step's first sentence names a List of bytes without fixing their order. The second sentence fixes it, and the
third and fourth give the NaN latitude, so the step's value depends on sentences that are not part of its expression.
RawBytesToNumeric says the same thing inside its expression. A reader, or a tool, has to fold the later sentences back
into the first one.

The NaN sentence also speaks of "each implementation distinguishable *NaN* value", while §6.1.6.1
(`#sec-ecmascript-language-types-number-type`) says:

> to ECMAScript code, all *NaN* values are indistinguishable from each other.

The sentence's intent is that one implementation always gives the same bytes for *NaN*.

## Examples

No observable difference: the order the step fixes is the order before step 5's reversal (when _isLittleEndian_ is
*false*), and the NaN bytes are the implementation's choice, which the step allows. With `ecma-run`:

```js
const f = new Float32Array([1.5]);
print([...new Uint8Array(f.buffer)]);   // 0,0,192,63 (the model's agent is little-endian)
```

## Proposed wording

Proposed: fold the order into the expression, as RawBytesToNumeric does, and keep the latitude as its own sentence
about one value:

```diff
-            1. Let _rawBytes_ be a List whose elements are the 2 bytes that are the result of converting _value_ to IEEE 754-2019 binary16 format using roundTiesToEven mode. The bytes are arranged in little endian order. If _value_ is *NaN*, _rawBytes_ may be set to any implementation chosen IEEE 754-2019 binary16 format NaN encoding. An implementation must always choose the same encoding for each implementation distinguishable *NaN* value.
+            1. Let _rawBytes_ be a List whose elements are the 2 bytes, in little-endian order, of the IEEE 754-2019 binary16 format encoding of the result of converting _value_ to IEEE 754-2019 binary16 format using roundTiesToEven mode. If _value_ is *NaN*, the encoding is an implementation-defined binary16 NaN encoding, the same each time.
```

The same for 2.a and 3.a; and for 4.d.i / 4.e.i, "the _n_ bytes, in little-endian order, of the binary (two's
complement) encoding of _intValue_".
