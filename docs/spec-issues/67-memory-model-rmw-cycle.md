# 67. §29 Memory Model: overlapping-RMW `ValueOfReadEvent` cycle non-termination, unquantified `reads-bytes-from`, and `HostEventSet`

- **Location:** §29.5.4 ComposeWriteEventBytes (`#sec-composewriteeventbytes`), step 3.d.ii; §29.5.5 ValueOfReadEvent
  (`#sec-valueofreadevent`); §29.6.2 reads-bytes-from (`#sec-reads-bytes-from`); §29.6.5 synchronizes-with
  (`#sec-synchronizes-with`), first bullet; §29.7.5 Valid Executions (`#sec-valid-executions`); §29.5.3 HostEventSet
  (`#sec-hosteventset`) and §29.6.4 host-synchronizes-with (`#sec-host-synchronizes-with`).
- **Kind:** non-terminating mutual recursion on candidate executions, unquantified relation variable, and set-domain
  contradiction.
- **Model erratum:** `MemoryModelRMWCycleAndRbf`, baked-in SpecTec reading proposed (layer `none`,
  `spec/spectec/prose/07-memory-model.spectec`). SpecTec defines `Compose` and `ValueOf` as a mutual inductive least
  fixpoint (so cyclic RMW byte reads evaluate `ValidChosenReads` to `False` instead of diverging), existentially
  quantifies `rbf : Rbf(E)` in `Valid`, converts `Tear Free Reads` step 1.a.i's `Assert:` into a boolean conjunct, and
  defines `HostSync` over `inHost`.
- **Upstream:** Checked 2026-11-19: none found for the RMW cycle or `HostEventSet` domain; PR #3321 (merged 2024-05,
  commit 1babaf809), "Editorial: Rework memory model relations", removed `[[ReadsBytesFrom]]` from Candidate Execution
  Records while leaving `reads-bytes-from` unquantified in §29.7.5.

## Text

`ComposeWriteEventBytes` (§29.5.4):

> 3.d.ii. Let _bytes_ be ValueOfReadEvent(_execution_, _writeEvent_).

`synchronizes-with` (§29.6.5):

> - For events _readEvent_ and _writeEvent_, _writeEvent_ synchronizes-with _readEvent_ in _execution_ if _readEvent_ reads-from _writeEvent_ in _execution_, _readEvent_.[[Order]] is ~seq-cst~, _writeEvent_.[[Order]] is ~seq-cst~, and _readEvent_ and _writeEvent_ have equal memory ranges.

`Valid Executions` (§29.7.5):

> A candidate execution _execution_ is a valid execution (or simply an execution) if all of the following are true.
> - _execution_ admits a happens-before Relation that is a strict partial order.

`HostEventSet` (§29.5.3) vs `host-synchronizes-with` (§29.6.4):

> 1. Return a new Set containing all elements of EventSet(_execution_) that are not in SharedDataBlockEventSet(_execution_).

> For a candidate execution _execution_, its host-synchronizes-with Relation is a host-provided strict partial order on host-specific Memory events that satisfies at least the following.
> - If _eventA_ host-synchronizes-with _eventB_ in _execution_, HostEventSet(_execution_) contains _eventA_ and _eventB_.

## Problem

1. **Non-terminating `ValueOfReadEvent` ↔ `ComposeWriteEventBytes` recursion on unequal overlapping RMWs.** `reads-bytes-from`
   only forbids direct 1-cycles (`_readEvent_ is not in _writes_`), not 2-cycles (`rmw1` reads byte 0 from `rmw2` and
   `rmw2` reads byte 0 from `rmw1`). When `rmw1` (e.g. 2-byte `Uint16Array` RMW on `[0, 2)`) and `rmw2` (4-byte
   `Uint32Array` RMW on `[0, 4)`) have *unequal* overlapping ranges, §29.6.5 `synchronizes-with` step 1.c does *not*
   order them! Thus `happens-before` remains a strict partial order, `Coherent Reads` holds, `Tear Free Reads` holds,
   and `Sequentially Consistent Atomics` holds — yet `Valid Chosen Reads` invokes `ValueOfReadEvent`, which diverges in
   infinite mutual recursion without returning `*true*` or `*false*`!
2. **Unquantified `reads-bytes-from` in §29.7.5.** PR #3321 removed `[[ReadsBytesFrom]]` from Candidate Execution
   Records, yet §29.7.5 `Valid Executions` quantifies `happens-before` without quantifying *"admits a reads-bytes-from
   function"*!
3. **`HostEventSet` includes `Synchronize` events.** §29.1 partitions Memory events into Shared Data Block, Synchronize
   (`EnterCriticalSection` / `LeaveCriticalSection`), and host-specific events, yet `HostEventSet` includes Synchronize
   events, contradicting §29.6.4's header.

## Examples

None run (the memory model is a declarative relation in `lean/Ecma/MemoryModel.lean`); SpecTec's inductive `ValueOf`
rejects cyclic RMW reads cleanly.

## Proposed wording

Require `reads-bytes-from` to be acyclic across RMW events (or order overlapping RMWs in `synchronizes-with`), quantify
`reads-bytes-from` in §29.7.5 `Valid Executions`, and exclude `Synchronize` events from `HostEventSet` (§29.5.3).

## test262

None (`test262` does not test formal §29 candidate-execution edge cases).
