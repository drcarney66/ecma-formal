# 23. Races: "it is not the case that both" is always true

- **Location:** §29.8 Races (`#sec-races`), step 1.a; §29.7.5 Valid Executions (`#sec-valid-executions`); §29.10
  Data Race Freedom (`#sec-data-race-freedom`).
- **Kind:** a condition that is always true under the clause's own definitions.
- **Model erratum:** `RacesNotBoth`, baked-in SpecTec reading literal (`Ecma.MemoryModel.Race`,
  `spec/spectec/prose/07-memory-model.spectec`); its note in `site/errata.json` gives the proposed wording below.
- **Upstream:** Checked 2026-11-19: PR #4021 (closed without merging, 2026-10), "Normative: exclude happens-before
  ordered events from races", proposed requiring that neither event happens-before the other; no issue was found
  (searched for "not the case that both" and "Races"). The wording came with PR #3321 (merged 2024-05, commit
  1babaf809), "Editorial: Rework memory model relations", which replaced "If the pairs (_E_, _D_) and (_D_, _E_) are
  not in _execution_.[[HappensBefore]]".

## Text

> 1. If _eventA_ and _eventB_ are not the same Shared Data Block event, then
>    a. If it is not the case that both _eventA_ happens-before _eventB_ in _execution_ and _eventB_ happens-before
>       _eventA_ in _execution_, then
>       i. If _eventA_ is either a WriteSharedMemory or ReadModifyWriteSharedMemory event, _eventB_ is either a
>          WriteSharedMemory or ReadModifyWriteSharedMemory event, and _eventA_ and _eventB_ do not have disjoint memory
>          ranges, then
>          1. Return *true*.
>       ii. If _eventA_ reads-from _eventB_ in _execution_ or _eventB_ reads-from _eventA_ in _execution_, then
>          1. Return *true*.
> 2. Return *false*.

§29.7.5:

> A candidate execution _execution_ is a valid execution (or simply an execution) if all of the following are true.
> …
> - _execution_ admits a happens-before Relation that is a strict partial order.

§29.10:

> The memory model guarantees sequential consistency of all events for data race free programs.

## Problem

Races are defined for an execution, whose happens-before is a strict partial order, hence asymmetric: "_eventA_
happens-before _eventB_ and _eventB_ happens-before _eventA_" never holds, and step 1.a's condition is always true.
Read literally, any two conflicting events race, including two writes that happens-before orders, such as two
writes of one agent in agent order. Data races, and with them the guarantee of §29.10, then cover every program
that writes shared memory twice at the same bytes. The intent is that neither event happens-before the other.

## Examples

None run: the definition is not observable through an engine, and the formal model defines the memory model in Lean
but does not run it. Under the literal text, this single-agent program has a data race (two ~unordered~ writes of
the same bytes, ordered by agent order), so it is not data race free:

```js
const ta = new Int32Array(new SharedArrayBuffer(4));
ta[0] = 1;
ta[0] = 2;
```

## Proposed wording

Proposed:

```diff
--- a/spec.html
+++ b/spec.html
@@ -53236,7 +53236,7 @@
     <p>For an execution _execution_ and events _eventA_ and _eventB_ that are contained in SharedDataBlockEventSet(_execution_), _eventA_ and _eventB_ are in a <em>race</em> if the following algorithm returns *true*.</p>
     <emu-alg>
       1. If _eventA_ and _eventB_ are not the same Shared Data Block event, then
-        1. If it is not the case that both _eventA_ happens-before _eventB_ in _execution_ and _eventB_ happens-before _eventA_ in _execution_, then
+        1. If neither _eventA_ happens-before _eventB_ in _execution_ nor _eventB_ happens-before _eventA_ in _execution_, then
           1. If _eventA_ is either a WriteSharedMemory or ReadModifyWriteSharedMemory event, _eventB_ is either a WriteSharedMemory or ReadModifyWriteSharedMemory event, and _eventA_ and _eventB_ do not have disjoint memory ranges, then
             1. Return *true*.
           1. If _eventA_ reads-from _eventB_ in _execution_ or _eventB_ reads-from _eventA_ in _execution_, then
```

## test262

No test: data race freedom is a property of all executions of a program, which test262 does not test.
