# 48. happens-before orders an ~init~ write only before events with *overlapping* ranges, which excludes the equal range of a 1-byte access

- **Location:** §29.6.6 happens-before (`#sec-happens-before`), the third condition, with §29.1 Memory Model
  Fundamentals (`#sec-memory-model-fundamentals`), the paragraph defining "overlapping", and §6.2.9.2
  CreateSharedByteDataBlock (`#sec-createsharedbytedatablock`), step 6.a; §29.6.5 synchronizes-with
  (`#sec-synchronizes-with`), its note; §29.7.2 Coherent Reads (`#sec-coherent-reads`); §29.7.4 Sequentially
  Consistent Atomics (`#sec-memory-order`); §29.7.5 Valid Executions (`#sec-valid-executions`); §29.8 Races
  (`#sec-races`); §29.9 Data Races (`#sec-data-races`).
- **Kind:** a definition that excludes a case its rule needs ("overlapping" excludes "equal").
- **Model erratum:** `InitHappensBeforeOverlap`, default reading literal; its readings: literal, proposed. The
  model's memory-model meaning (`HB.init` in `lean/Ecma/MemoryModel.lean`) keeps the text's "overlapping"; the
  proposed reading is the diff under "Proposed wording", which the erratum carries as a note (the rule is a list
  item, not an algorithm step), and it is not switched at run time.
- **Upstream:** Checked 2026-11-19: none found (searched for "happens-before" with init, and "overlapping"). The rule
  has its present form from PR #3321 (merged 2024-05, commit 1babaf809); before it, it read "[[HappensBefore]]
  contains (_E_, _D_) if _E_.[[Order]] is ~init~ and _E_ and _D_ have overlapping ranges". PR #3396 (merged 2025-11,
  commit f1bdd8c02) renamed "range" to "memory range".

## Text

§29.1, the memory range definitions:

> Let the memory range of a Shared Data Block event _e_ be the Set of all integers in the interval from
> _e_.[[ByteIndex]] (inclusive) to _e_.[[ByteIndex]] + _e_.[[ElementSize]] (exclusive). Two events' memory ranges are
> equal when the events have the same [[Block]], [[ByteIndex]], and [[ElementSize]]. Two events' memory ranges are
> overlapping when the events have the same [[Block]], the ranges are not equal, and their intersection is non-empty.
> Two events' memory ranges are disjoint when the events do not have the same [[Block]] or their ranges are neither
> equal nor overlapping.

§29.6.6 happens-before:

> For events _eventA_ and _eventB_, _eventA_ happens-before _eventB_ in _execution_ if any of the following conditions
> are true.
>
> - _eventA_ is-agent-order-before _eventB_ in _execution_.
> - _eventA_ synchronizes-with _eventB_ in _execution_.
> - SharedDataBlockEventSet(_execution_) contains both _eventA_ and _eventB_, _eventA_.[[Order]] is ~init~, and
>   _eventA_ and _eventB_ have overlapping memory ranges.
> - There is an event _eventC_ such that _eventA_ happens-before _eventC_ and _eventC_ happens-before _eventB_ in
>   _execution_.

§29.6.5 synchronizes-with, after its definition:

> In a candidate execution _execution_, ~init~ events do not participate in this Relation and are instead constrained
> directly by happens-before.

CreateSharedByteDataBlock:

> 6. For each index _index_ of _dataBlock_, do
>    a. Append WriteSharedMemory { [[Order]]: ~init~, [[NoTear]]: *true*, [[Block]]: _dataBlock_, [[ByteIndex]]:
>       _index_, [[ElementSize]]: 1, [[Payload]]: _zero_ } to _eventsRecord_.[[EventList]].

The same chapter already writes the complement the other way, in Races (§29.8, step 1.a.i): "_eventA_
and _eventB_ do not have disjoint memory ranges".

## Problem

The ~init~ writes are one per byte: [[ElementSize]] is 1 and [[ByteIndex]] is the byte's index. The third condition
orders such a write _init_<sub>i</sub> before an event _eventB_ only if their memory ranges are *overlapping*, and the
definition of "overlapping" says "the ranges are not equal". An event of [[ElementSize]] 1 at [[ByteIndex]] _i_ in the
same block (a read or write through an `Int8Array`, `Uint8Array` or `Uint8ClampedArray`, or `DataView`'s
`getInt8`/`setInt8`/`getUint8`/`setUint8`, or `Atomics` on those) has a memory range *equal* to _init_<sub>i</sub>'s, so
the third condition does not apply to it. An event of any larger size at or around _i_ has an intersecting, unequal
range, so it does. The rule therefore holds for every access size except the one that the ~init~ events themselves
have, which §29.6.5's note ("~init~ events … are instead constrained directly by happens-before") says happens-before is
meant to constrain.

What is left to order _init_<sub>i</sub> before a 1-byte event _eventB_ is the other three conditions: agent order
(true when _eventB_ is in the agent that created the block, whose EventList holds the ~init~ events), and
synchronizes-with or a chain through the host's host-synchronizes-with (§29.1's note names "sending a SharedArrayBuffer from one agent to another" among the host-specific synchronizing
events a host should account for). An agent
that obtains the block with no such chain is the case the third condition exists for, and for 1-byte events it
orders nothing.

Take such an agent, with a 1-byte write _W_ followed in its agent order by a 1-byte read _R_ of the same byte, and the
candidate execution in which _R_ reads-bytes-from _init_<sub>i</sub> (and so reads 0):

- Valid Chosen Reads holds: the chosen value is that of _init_<sub>i</sub>.
- Coherent Reads (§29.7.2) fails only if _R_ happens-before _init_<sub>i</sub> (no) or some write _value_ at the byte
  has _init_<sub>i</sub> happens-before _value_ and _value_ happens-before _R_. _W_ happens-before _R_ by agent order,
  but _init_<sub>i</sub> happens-before _W_ needs the third condition, which does not apply. So it holds.
- Sequentially Consistent Atomics (§29.7.4): the three disjuncts with a ~seq-cst~ _value_ all need _writeEvent_
  (here _init_<sub>i</sub>) to synchronize-with or happen-before the read or the write; none does. So it holds even when
  _W_ and _R_ are `Atomics.store` and `Atomics.load`.

So, literally, `Atomics.store(i8, 0, 1)` followed by `Atomics.load(i8, 0)` in that agent may return 0, the initial
value, which is the coherence the rule is there to give. With an `Int16Array` over the same block, the same two
accesses (`Atomics.store(i16, 0, 1)`, `Atomics.load(i16, 0)`) overlap _init_<sub>0</sub> and _init_<sub>1</sub>,
`init` happens-before the write, and the load cannot return 0.

The same gap shows in Races (§29.8) and so in data races (§29.9): _init_<sub>i</sub> and a 1-byte write _W_ not ordered by
happens-before race (step 1.a.i: a write and a write whose ranges are not disjoint), and, because an ~init~ event is
not ~seq-cst~, they are in a data race (step 1.a), even if _W_ is ~seq-cst~. A program whose accesses are all
`Atomics` calls on an `Int8Array` is then not data race free in an agent with no chain from the creator, while the
same program on an `Int32Array` is, assuming the corrected Races step 1.a of [23](23-races-not-both.md)
(literally, "it is not the case that both _eventA_ happens-before _eventB_ in _execution_ and _eventB_
happens-before _eventA_ in _execution_" always holds, so _init_<sub>i</sub> races every non-disjoint write of any
size, ~init~ is not ~seq-cst~, and neither program is data race free).

An embedding that sends a block with a host-synchronizes-with edge never reaches this case, so an engine whose host
always supplies the edge is not affected. The text is the problem, not an implementation: nothing requires every channel by which an agent can obtain a
block to provide that edge ("hosts can add host-specific synchronizing events"), and a reader who takes the third
condition as "init writes happen before everything that touches their byte" gets a different model from the one
the text defines.

## Examples

No program is run here: the case needs a host that hands an agent a block with no host-synchronizes-with edge from
its creator, which a host that sends blocks supplies, so no engine was run for it; the formal model's memory-model
meaning is a relation on candidate executions and does not run programs. The shape under the literal text (the text's
reading, not a program that behaves so):

```js
// agent B, handed a SharedArrayBuffer sab by a channel with no host-synchronizes-with edge from its creator
const i8 = new Int8Array(sab);
Atomics.store(i8, 0, 1);
Atomics.load(i8, 0); // literally: 0 is allowed (the load reads init_0)
```

## Proposed wording

Proposed: make the condition the complement of disjoint, as Races writes it, and exclude the event itself: an
~init~ event's own range is equal to itself, so "do not have disjoint memory ranges" alone makes _init_<sub>i</sub>
happens-before _init_<sub>i</sub>, and a strict partial order (the second condition of §29.7.5 Valid Executions)
would then fail for every execution that creates a block.

```diff
--- a/spec.html
+++ b/spec.html
@@ -53121,1 +53121,1 @@
-            <li>SharedDataBlockEventSet(_execution_) contains both _eventA_ and _eventB_, _eventA_.[[Order]] is ~init~, and _eventA_ and _eventB_ have overlapping memory ranges.</li>
+            <li>SharedDataBlockEventSet(_execution_) contains both _eventA_ and _eventB_, _eventA_.[[Order]] is ~init~, _eventA_ and _eventB_ are not the same Shared Data Block event, and _eventA_ and _eventB_ do not have disjoint memory ranges.</li>
```

Two ~init~ events never have equal ranges but are different events, so for them the new wording gives the same
result as the old (their ranges are disjoint); for a non-~init~ _eventB_ with an equal range the new wording adds the
edge. The definitions of "overlapping" and "disjoint" stay as they are: the synchronizes-with, Sequentially Consistent
Atomics and data race clauses (§29.6.5, §29.7.4, §29.9) use "equal" and "overlapping" apart on purpose.

## test262

No test: the difference needs a host without a host-synchronizes-with edge from the creator to the receiver, which test262
cannot construct.
