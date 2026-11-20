# 43. AllocateSharedArrayBuffer stores a growable buffer's length with SetValueInBuffer on a Shared Data Block

- **Location:** §25.2.2.1 AllocateSharedArrayBuffer (`#sec-allocatesharedarraybuffer`), step 9.c, against §25.1.3.18
  SetValueInBuffer (`#sec-setvalueinbuffer`), its first parameter.
- **Kind:** type error (a Shared Data Block where an ArrayBuffer or SharedArrayBuffer is required).
- **Model erratum:** `AllocateSharedArrayBufferByteLengthStore`, default reading test262; its readings: literal,
  test262, proposed. The test262 and proposed readings are the same steps, the proposed wording below.
- **Upstream:** Checked 2026-11-19: PR #4023 (closed without merging, 2026-10), "Editorial: initialize shared
  byte-length data with a memory event", proposed replacing the SetValueInBuffer call by a WriteSharedMemory event; no
  issue was found (searched for "AllocateSharedArrayBuffer"). The step came with PR #3116 (merged 2023-10, commit
  a9ae96eda); PR #3976 (open, 2026-09), "Editorial: Use "Internal Slots" tables for more object types", leaves it as
  it is.

## Text

> 9. If _allocatingGrowableBuffer_ is *true*, then
>     a. Assert: _byteLength_ ≤ _maxByteLength_.
>     b. Let _byteLengthBlock_ be ? CreateSharedByteDataBlock(8).
>     c. Perform SetValueInBuffer(_byteLengthBlock_, 0, ~biguint64~, ℤ(_byteLength_), *true*, ~seq-cst~).
>     d. Set _obj_.[[ArrayBufferByteLengthData]] to _byteLengthBlock_.

SetValueInBuffer takes "_arrayBuffer_: an ArrayBuffer or SharedArrayBuffer", and its steps begin:

> 1. Assert: IsDetachedBuffer(_arrayBuffer_) is *false*.
> …
> 4. Let _block_ be _arrayBuffer_.[[ArrayBufferData]].

## Problem

CreateSharedByteDataBlock returns a Shared Data Block, a data block value with no internal slots, not a
SharedArrayBuffer. Step 9.c passes it to SetValueInBuffer outside its parameter's type: IsDetachedBuffer (step 1)
and step 4 read its [[ArrayBufferData]], which it does not have, so the step has no defined result and every
growable SharedArrayBuffer construction reaches it. The other readers and writers of the same block,
ArrayBufferByteLength (§25.1.3.2) and SharedArrayBuffer.prototype.grow (§25.2.5.3), use the Shared Data Block
operations GetRawBytesFromSharedBlock and AtomicCompareExchangeInSharedBlock on the block itself. The intent is
clear: write the length into the block as a seq-cst 8-byte event, as SetValueInBuffer's shared branch would for a
SharedArrayBuffer whose [[ArrayBufferData]] is the block.

## Examples

[examples/43-allocatesharedarraybuffer-byte-length.js](examples/43-allocatesharedarraybuffer-byte-length.js)
(outputs: [RESULTS.md](examples/RESULTS.md#43-allocatesharedarraybuffer-byte-lengthjs)):

```js
var sab = new SharedArrayBuffer(4, { maxByteLength: 16 });
print(sab.growable + " " + sab.byteLength + " " + sab.maxByteLength);
sab.grow(8);
print(sab.byteLength + " " + new Int32Array(sab).length);
```

| | construction | `growable byteLength maxByteLength` | after `grow(8)` |
|---|---|---|---|
| literal step 9.c | no defined result (SetValueInBuffer on a Shared Data Block) | — | — |
| V8, SpiderMonkey, JavaScriptCore | succeeds | `true 4 16` | `8 2` |
| formal model (test262 and proposed readings) | succeeds | `true 4 16` | `8 2` |
| formal model (literal reading) | the run stops in SetValueInBuffer (`stop: sortError sec-setvalueinbuffer#0 4`) | — | — |

## Proposed wording

The steps of SetValueInBuffer's shared branch, on the block itself (IsNoTearConfiguration(~biguint64~, ~seq-cst~) is
*true*):

```diff
--- a/spec.html
+++ b/spec.html
@@ -45903,7 +45903,11 @@
           1. If _allocatingGrowableBuffer_ is *true*, then
             1. Assert: _byteLength_ ≤ _maxByteLength_.
             1. Let _byteLengthBlock_ be ? CreateSharedByteDataBlock(8).
-            1. Perform SetValueInBuffer(_byteLengthBlock_, 0, ~biguint64~, ℤ(_byteLength_), *true*, ~seq-cst~).
+            1. Let _agentRecord_ be the Agent Record of the surrounding agent.
+            1. Let _rawBytes_ be NumericToRawBytes(~biguint64~, ℤ(_byteLength_), _agentRecord_.[[LittleEndian]]).
+            1. Let _execution_ be _agentRecord_.[[CandidateExecution]].
+            1. Let _eventsRecord_ be the Agent Events Record of _execution_.[[EventsRecords]] whose [[AgentSignifier]] is AgentSignifier().
+            1. Append WriteSharedMemory { [[Order]]: ~seq-cst~, [[NoTear]]: *true*, [[Block]]: _byteLengthBlock_, [[ByteIndex]]: 0, [[ElementSize]]: 8, [[Payload]]: _rawBytes_ } to _eventsRecord_.[[EventList]].
             1. Set _obj_.[[ArrayBufferByteLengthData]] to _byteLengthBlock_.
             1. Set _obj_.[[ArrayBufferMaxByteLength]] to _maxByteLength_.
           1. Else,
```

A shorter alternative is an abstract operation that writes a value into a Shared Data Block, shared by this step
and SetValueInBuffer's shared branch.

## test262

No test checks the step's event itself, but 14 test files construct a growable SharedArrayBuffer directly (eight in
`built-ins/SharedArrayBuffer/prototype`, among them `grow/grow-larger-size.js`, three in `built-ins/Atomics` and
three in `staging/built-ins`), and none of them has a defined result under the literal step.
