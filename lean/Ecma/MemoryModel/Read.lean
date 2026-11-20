module

public import Ecma.MemoryModel

@[expose] public section

/-!
# A read added to a candidate execution

A shared read appends its event to an Agent Events Record's [[EventList]] and its Chosen Value Record
to [[ChosenValues]] (GetRawBytesFromSharedBlock, GetModifySetValueInBuffer,
AtomicCompareExchangeInSharedBlock, CopyDataBlockBytes): `Exec.snoc`, the new event `none` and the
others `some`. Over it: the claim of law L2 (`ReadsValid`).
-/

namespace Ecma.MemoryModel

variable {M : Model} {E : Type}

/-- The new event of a shared read: its kind and fields. -/
structure NewEvent (M : Model) where
  kind : Kind
  order : Order
  noTear : Bool
  block : M.Addr
  byteIndex : M.Math
  elementSize : M.Math
  payload : List M.Math
  modify : List M.Math → List M.Math → Option (List M.Math)

/-- A read event of a shared read: a ReadSharedMemory or ReadModifyWriteSharedMemory event, not
~init~, its [[ByteIndex]] a non-negative integer, aligned where it cannot tear (tear free reads,
step 1.a.i). -/
structure NewEvent.IsRead (r : NewEvent M) : Prop where
  kind : r.kind = .read ∨ r.kind = .rmw
  order : r.order ≠ .init
  byteIndex : ∃ n, r.byteIndex = M.ofNat n
  aligned : r.noTear = true → M.isInt (M.div r.byteIndex r.elementSize) = true

/-- The `i`th Agent Events Record `er`, the new event `none` appended where `i` is `k`. -/
def EventsRecord.snoc (k i : Nat) (er : EventsRecord E) : EventsRecord (Option E) :=
  ⟨er.events.map some ++ (if i = k then [none] else []), er.syncs.map fun p => (some p.1, some p.2)⟩

/-- `x` with the event `r` (`none`) appended to the [[EventList]] of its `k`th Agent Events Record,
and the Chosen Value Record of `r` and `cv` to its [[ChosenValues]]. -/
def Exec.snoc (x : Exec M E) (k : Nat) (r : NewEvent M) (cv : List M.Math) : Exec M (Option E) where
  records := x.records.mapIdx (EventsRecord.snoc k)
  chosen := x.chosen.map (fun c => (some c.1, c.2)) ++ [(none, cv)]
  kind | some e => x.kind e | none => r.kind
  order | some e => x.order e | none => r.order
  noTear | some e => x.noTear e | none => r.noTear
  block | some e => x.block e | none => r.block
  byteIndex | some e => x.byteIndex e | none => r.byteIndex
  elementSize | some e => x.elementSize e | none => r.elementSize
  payload | some e => x.payload e | none => r.payload
  modify | some e => x.modify e | none => r.modify

/-- `rbf`, the new event reading from `ws`. -/
def Rbf.snoc (rbf : Rbf E) (ws : List E) : Rbf (Option E)
  | some e => (rbf e).map some
  | none => ws.map some

/-- A Relation on the events but the new one. -/
def Rel.lift (r : Rel E) : Rel (Option E)
  | some a, some b => r a b
  | _, _ => False

/-- Law L2's claim: with the read `r` appended to the `k`th Agent Events Record, reading its bytes
from `ws`, its Chosen Value Record the byte values ComposeWriteEventBytes composes of them, `x` is a
valid execution with `rbf` and `hsw`. -/
def ReadsValid (x : Exec M E) (rbf : Rbf E) (hsw : Rel E) (k : Nat) (r : NewEvent M) (ws : List E) : Prop :=
  ∀ cv, (∀ c ∈ cv, ∃ n, c = M.ofNat n) → Compose x rbf r.byteIndex ws cv → ValidWith (x.snoc k r cv) (rbf.snoc ws) (Rel.lift hsw)

end Ecma.MemoryModel
