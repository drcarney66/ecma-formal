# 22. reads-bytes-from names an unbound `_result_`

The pinned text no longer has this defect: its second condition names _readEvent_, and the model's erratum
`ReadsBytesFromUnboundResult` is retired.

- **Location:** §29.6.2 reads-bytes-from (`#sec-reads-bytes-from`), the second condition.
- **Kind:** an unbound name (a condition that refers to a variable nothing introduces).
- **Model erratum:** none: `ReadsBytesFromUnboundResult` is retired, and the model reads the pinned text as written. It had one reading, `proposed`,
  which is the pinned text: the memory model's meaning (`Rbf.Valid`, `lean/Ecma/MemoryModel.lean`) already read
  "_readEvent_ is not in _writes_".
- **Upstream:** Checked 2026-11-19: fixed by PR #4064, "Editorial: Fix an incorrect alias name in reads-bytes-from",
  merged 2026-11-08 as commit d8cb87726, which replaced _result_ by _readEvent_. The unbound name came with PR #3789
  (merged 2026-04, commit bab3fbf29), which renamed _R_ to _readEvent_ and _Ws_ to _writes_ but the condition's _R_ to
  _result_. PR #4025 (closed without merging, 2026-10) had proposed the same change.

## Text

The pinned text:

> For each ReadSharedMemory or ReadModifyWriteSharedMemory event _readEvent_ in SharedDataBlockEventSet(_execution_),
> reads-bytes-from(_readEvent_) in _execution_ is a List of length _readEvent_.[[ElementSize]] whose elements are
> WriteSharedMemory or ReadModifyWriteSharedMemory events _writes_ such that all of the following are true.
>
> - Each event _writeEvent_ with index _i_ in _writes_ has _readEvent_.[[ByteIndex]] + _i_ in its memory range.
> - _readEvent_ is not in _writes_.

The second condition before the fix:

<!-- quote: ECMA-262 before the fix -->
> - _result_ is not in _writes_.

## Problem

The clause binds _execution_, _readEvent_, _writes_, _writeEvent_ and _i_. No _result_ was in scope, so the second
condition had no meaning as written. Its intent is the pinned text's: a ReadModifyWriteSharedMemory event does not read
the bytes it writes itself. Without it, an Atomics read-modify-write could read from its own write.

## Examples

None run: the condition constrains the candidate executions of the memory model, which no single-agent program and no
engine output shows. The formal model defines the memory model in Lean but does not run it.

## Proposed wording

None: the pinned text reads "_readEvent_ is not in _writes_", the wording this write-up proposed.

## test262

No test separates the readings: a test would need an execution in which a read-modify-write reads its own write.
