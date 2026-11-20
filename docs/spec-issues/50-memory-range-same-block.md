# 50. reads-bytes-from and coherent reads ask only for a byte index in a memory range, which names no [[Block]]

- **Location:** §29.1 Memory Model Fundamentals (`#sec-memory-model-fundamentals`), the paragraph defining "memory
  range"; §29.6.2 reads-bytes-from (`#sec-reads-bytes-from`), the first condition; §29.7.2 Coherent Reads
  (`#sec-coherent-reads`), step 1.c.ii.
- **Kind:** a missing condition (a test against a Set of integers that drops the event's [[Block]]).
- **Model erratum:** `MemoryRangeSameBlock`, default reading proposed; its readings: literal, proposed. The model's
  memory-model meaning (`Rbf.Valid` and `CoherentReads` in `lean/Ecma/MemoryModel.lean`) reads the proposed
  wording; the readings are not switched at run time.
- **Upstream:** Checked 2026-11-19: none found (searched for "memory range"; the hits rename or link the term).

## Text

§29.1:

> Let the memory range of a Shared Data Block event _e_ be the Set of all integers in the interval from
> _e_.[[ByteIndex]] (inclusive) to _e_.[[ByteIndex]] + _e_.[[ElementSize]] (exclusive). Two events' memory ranges are
> equal when the events have the same [[Block]], [[ByteIndex]], and [[ElementSize]]. …

§29.6.2 reads-bytes-from:

> - Each event _writeEvent_ with index _i_ in _writes_ has _readEvent_.[[ByteIndex]] + _i_ in its memory range.

§29.7.2 Coherent Reads, step 1.c.ii:

> 1.c.ii. If there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event _value_ that has _byteLocation_ in
> its memory range such that _writeEvent_ happens-before _value_ in _execution_ and _value_ happens-before
> _readEvent_ in _execution_, then
>     1. Return *false*.

## Problem

A memory range is a Set of integers, so "has _n_ in its memory range" holds for an event on any Shared Data Block whose
byte indices include _n_. The relations "equal", "overlapping" and "disjoint" compare [[Block]]s explicitly; these two
tests do not. Read literally:

- reads-bytes-from lets a read take its bytes from a write to another block at the same indices;
- coherent reads rejects an execution in which a write to another block at the read's index happens between the
  write the read reads from and the read.

Together they change single-agent results. With two one-byte SharedArrayBuffers in one agent:

```js
const a = new Int8Array(new SharedArrayBuffer(1));
const b = new Int8Array(new SharedArrayBuffer(1));
b[0] = 1;
a[0]; // literally 1
```

The candidates for the read of `a[0]` are a's ~init~ write, b's ~init~ write and the write of `b[0]`. Both ~init~
writes happen-before the write of `b[0]` (agent order), which happens-before the read and has byte 0 in its memory
range, so step 1.c.ii rejects both; the only coherent choice is the write to b, and the read returns 1. Under the proposed
wording it returns 0, a's initial value.

## Examples

The program above: literally `1`, under the proposed wording `0`. It is not among the recorded examples
([RESULTS.md](examples/RESULTS.md)), and the formal model's memory-model meaning is a relation on candidate
executions, not a program the driver runs.

## Proposed wording

Proposed: name the [[Block]] in both tests.

```diff
--- a/spec.html
+++ b/spec.html
@@ -53046,1 +53046,1 @@
-            <li>Each event _writeEvent_ with index _i_ in _writes_ has _readEvent_.[[ByteIndex]] + _i_ in its memory range.</li>
+            <li>Each event _writeEvent_ with index _i_ in _writes_ has _readEvent_.[[Block]] as its [[Block]] and _readEvent_.[[ByteIndex]] + _i_ in its memory range.</li>
@@ -53164,1 +53164,1 @@
-            1. If there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event _value_ that has _byteLocation_ in its memory range such that _writeEvent_ happens-before _value_ in _execution_ and _value_ happens-before _readEvent_ in _execution_, then
+            1. If there exists a WriteSharedMemory or ReadModifyWriteSharedMemory event _value_ whose [[Block]] is _readEvent_.[[Block]] and that has _byteLocation_ in its memory range such that _writeEvent_ happens-before _value_ in _execution_ and _value_ happens-before _readEvent_ in _execution_, then
```

The alternative, a memory range that is a Set of (block, index) pairs, changes the definitions of "equal",
"overlapping" and "disjoint" too; the two-line fix leaves them as they are.

## test262

Any test that, in one agent, writes one SharedArrayBuffer and then reads another at the same index separates the
readings: under the literal text the read takes the other buffer's value. No test is written to check this case.
