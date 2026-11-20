module

public import Ecma.Model

@[expose] public section

/-!
# The memory model (§29): relations and validity of a candidate execution

A candidate execution as the memory model sees it (`Exec`): its Agent Events Records, its Chosen
Value Records and its events' fields, each event by identity. Over it, with a reads-bytes-from
function and the host's host-synchronizes-with: the relations of §29.6, the properties of §29.7
and races, data races and data race freedom (§29.8-29.10). The errata, each at one reading (none of them
switchable): MemoryRangeSameBlock at its proposed text (`Rbf.Valid`, `CoherentReads`), RacesNotBoth and
InitHappensBeforeOverlap at their literal text (`Race`, `HB.init`).
ValueOfReadEvent and ComposeWriteEventBytes are a least fixpoint (`ValueOf`, `Compose`): a cycle of
ReadModifyWriteSharedMemory events reading from each other has no value, so it fails valid chosen reads.
-/

namespace Ecma.MemoryModel

/-- A Memory event's kind (§29.1). -/
inductive Kind where
  | read
  | write
  | rmw
  | sync
  | host
  deriving DecidableEq, Repr

/-- A Shared Data Block event's [[Order]]. -/
inductive Order where
  | seqCst
  | unordered
  | init
  deriving DecidableEq, Repr

/-- An Agent Events Record (§29.2): its [[EventList]] and [[AgentSynchronizesWith]]. -/
structure EventsRecord (E : Type) where
  events : List E
  syncs : List (E × E)

/-- A candidate execution (§29.4) and the fields of its events (§29.1), events `E` by identity. -/
structure Exec (M : Model) (E : Type) where
  records : List (EventsRecord E)
  /-- [[ChosenValues]]: each Chosen Value Record's [[Event]] and [[ChosenValue]] -/
  chosen : List (E × List M.Math)
  kind : E → Kind
  order : E → Order
  noTear : E → Bool
  block : E → M.Addr
  byteIndex : E → M.Math
  elementSize : E → M.Math
  payload : E → List M.Math
  /-- [[ModifyOp]] called on a List of byte values and [[Payload]]; none where the call has no result -/
  modify : E → List M.Math → List M.Math → Option (List M.Math)

/-- A reads-bytes-from function (§29.6.2). -/
abbrev Rbf (E : Type) := E → List E

/-- A Relation on Memory events. -/
abbrev Rel (E : Type) := E → E → Prop

/-- The transitive closure of a Relation. -/
inductive Plus {E : Type} (r : Rel E) : Rel E where
  | step {a b : E} : r a b → Plus r a b
  | trans {a b c : E} : Plus r a b → Plus r b c → Plus r a c

/-- A strict partial order: irreflexive and transitive. -/
structure StrictPartialOrder {E : Type} (r : Rel E) : Prop where
  irrefl : ∀ a, ¬ r a a
  trans : ∀ a b c, r a b → r b c → r a c

/-- `l[k]` for a mathematical value `k`: the element at the integer index `k`. -/
def At {M : Model} (l : List M.Math) (k : M.Math) (b : M.Math) : Prop :=
  ∃ i : Nat, M.eq (M.ofNat i) k = true ∧ l[i]? = some b

variable {M : Model} {E : Type} (x : Exec M E)

/-- A Shared Data Block event: a ReadSharedMemory, WriteSharedMemory or ReadModifyWriteSharedMemory. -/
def isSdb (e : E) : Prop := x.kind e = .read ∨ x.kind e = .write ∨ x.kind e = .rmw

/-- A read event: a ReadSharedMemory or a ReadModifyWriteSharedMemory. -/
def isRead (e : E) : Prop := x.kind e = .read ∨ x.kind e = .rmw

/-- A write event: a WriteSharedMemory or a ReadModifyWriteSharedMemory. -/
def isWrite (e : E) : Prop := x.kind e = .write ∨ x.kind e = .rmw

/-- EventSet(_execution_) contains `e` (§29.5.1). -/
def inEvents (e : E) : Prop := ∃ r ∈ x.records, e ∈ r.events

/-- SharedDataBlockEventSet(_execution_) contains `e` (§29.5.2). -/
def inSdb (e : E) : Prop := inEvents x e ∧ isSdb x e

/-- HostEventSet(_execution_) contains `e` (§29.5.3). -/
def inHost (e : E) : Prop := inEvents x e ∧ ¬ inSdb x e

/-- `e` has `b` in its memory range: an integer from [[ByteIndex]] (inclusive) to [[ByteIndex]] +
[[ElementSize]] (exclusive) (§29.1). -/
def inRange (e : E) (b : M.Math) : Prop :=
  M.isInt b = true ∧ M.lt b (x.byteIndex e) = false ∧
    M.lt b (M.add (x.byteIndex e) (x.elementSize e)) = true

/-- Equal memory ranges: the same [[Block]], [[ByteIndex]] and [[ElementSize]] (§29.1). -/
def rangesEqual (a b : E) : Prop :=
  x.block a = x.block b ∧ M.eq (x.byteIndex a) (x.byteIndex b) = true ∧
    M.eq (x.elementSize a) (x.elementSize b) = true

/-- Overlapping memory ranges: the same [[Block]], not equal, a common byte (§29.1). -/
def rangesOverlapping (a b : E) : Prop :=
  x.block a = x.block b ∧ ¬ rangesEqual x a b ∧ ∃ k, inRange x a k ∧ inRange x b k

/-- Disjoint memory ranges: another [[Block]], or neither equal nor overlapping (§29.1). -/
def rangesDisjoint (a b : E) : Prop :=
  x.block a ≠ x.block b ∨ (¬ rangesEqual x a b ∧ ¬ rangesOverlapping x a b)

/-- `a` is-agent-order-before `b` (§29.6.1): before it in some Agent Events Record's [[EventList]]. -/
def agentOrder (a b : E) : Prop :=
  ∃ r ∈ x.records, a ∈ r.events ∧ b ∈ r.events ∧
    ∃ i j : Nat, i < j ∧ r.events[i]? = some a ∧ r.events[j]? = some b

/-- `rbf` is a reads-bytes-from function of `x` (§29.6.2): each read event's List has its
[[ElementSize]] write events, the `i`th of its [[Block]] (MemoryRangeSameBlock) with [[ByteIndex]] +
`i` in its memory range, and not the read event itself ("_readEvent_ is not in _writes_"). -/
def Rbf.Valid (rbf : Rbf E) : Prop :=
  ∀ r, inSdb x r → isRead x r →
    M.eq (M.ofNat (rbf r).length) (x.elementSize r) = true ∧
    (∀ w ∈ rbf r, inSdb x w ∧ isWrite x w) ∧
    (∀ (i : Nat) w, (rbf r)[i]? = some w →
      x.block w = x.block r ∧ inRange x w (M.add (x.byteIndex r) (M.ofNat i))) ∧
    r ∉ rbf r

/-- `r` reads-from `w` (§29.6.3). -/
def readsFrom (rbf : Rbf E) (r w : E) : Prop := inSdb x r ∧ inSdb x w ∧ w ∈ rbf r

/-- `hsw` is a host-synchronizes-with of `x` (§29.6.4): a strict partial order on host-specific
events with no cycle in its union with is-agent-order-before. -/
def HostSync (hsw : Rel E) : Prop :=
  StrictPartialOrder hsw ∧ (∀ a b, hsw a b → inHost x a ∧ inHost x b) ∧
    ∀ a, ¬ Plus (fun a b => hsw a b ∨ agentOrder x a b) a a

/-- synchronizes-with (§29.6.5): the least Relation closed under its three rules. -/
inductive SyncWith (rbf : Rbf E) (hsw : Rel E) : Rel E where
  | rf {r w : E} : readsFrom x rbf r w → x.order r = .seqCst → x.order w = .seqCst →
      rangesEqual x r w → SyncWith rbf hsw w r
  | agent {a b : E} (rec : EventsRecord E) : rec ∈ x.records → (a, b) ∈ rec.syncs → SyncWith rbf hsw a b
  | host {a b : E} : hsw a b → SyncWith rbf hsw a b

/-- happens-before (§29.6.6): the least Relation closed under its four rules. -/
inductive HB (rbf : Rbf E) (hsw : Rel E) : Rel E where
  | agent {a b : E} : agentOrder x a b → HB rbf hsw a b
  | sync {a b : E} : SyncWith x rbf hsw a b → HB rbf hsw a b
  | init {a b : E} : inSdb x a → inSdb x b → x.order a = .init → rangesOverlapping x a b →
      HB rbf hsw a b
  | trans {a b c : E} : HB rbf hsw a c → HB rbf hsw c b → HB rbf hsw a b

mutual
/-- ComposeWriteEventBytes(_execution_, `loc`, `ws`) returns `bs` (§29.5.4). -/
inductive Compose (rbf : Rbf E) : M.Math → List E → List M.Math → Prop where
  | nil {loc : M.Math} : Compose rbf loc [] []
  | write {loc byte : M.Math} {w : E} {ws : List E} {bs : List M.Math} : inRange x w loc →
      x.kind w = .write → At (x.payload w) (M.sub loc (x.byteIndex w)) byte →
      Compose rbf (M.add loc (M.ofNat 1)) ws bs → Compose rbf loc (w :: ws) (byte :: bs)
  | rmw {loc byte : M.Math} {w : E} {ws : List E} {bs bytes mod : List M.Math} : inRange x w loc →
      x.kind w = .rmw → ValueOf rbf w bytes → x.modify w bytes (x.payload w) = some mod →
      At mod (M.sub loc (x.byteIndex w)) byte → Compose rbf (M.add loc (M.ofNat 1)) ws bs →
      Compose rbf loc (w :: ws) (byte :: bs)

/-- ValueOfReadEvent(_execution_, `r`) returns `v` (§29.5.5). -/
inductive ValueOf (rbf : Rbf E) : E → List M.Math → Prop where
  | mk {r : E} {v : List M.Math} : (∀ w ∈ rbf r, isWrite x w) →
      M.eq (M.ofNat (rbf r).length) (x.elementSize r) = true →
      Compose rbf (x.byteIndex r) (rbf r) v → ValueOf rbf r v
end

/-- `x` has valid chosen reads (§29.7.1): the algorithm returns *true*. Each read event has one
Chosen Value Record, whose [[ChosenValue]] is the value it reads, byte for byte. -/
def ValidChosenReads (rbf : Rbf E) : Prop :=
  ∀ r, inSdb x r → isRead x r →
    ∃ (i : Nat) (cv : List M.Math), x.chosen[i]? = some (r, cv) ∧
      (∀ (j : Nat) cv', x.chosen[j]? = some (r, cv') → j = i) ∧
      ∃ v, ValueOf x rbf r v ∧ cv.length = v.length ∧
        ∀ (k : Nat) a b, cv[k]? = some a → v[k]? = some b → M.eq a b = true

/-- `x` has coherent reads (§29.7.2): no read event reads a byte from a write it happens-before, or
from one that another write of the byte, on its [[Block]] (step 1.c.ii; MemoryRangeSameBlock),
happens-between. -/
def CoherentReads (rbf : Rbf E) (hsw : Rel E) : Prop :=
  ∀ r, inSdb x r → isRead x r → ∀ (i : Nat) w, (rbf r)[i]? = some w →
    ¬ HB x rbf hsw r w ∧
    ¬ ∃ v, isWrite x v ∧ x.block v = x.block r ∧ inRange x v (M.add (x.byteIndex r) (M.ofNat i)) ∧
      HB x rbf hsw w v ∧ HB x rbf hsw v r

/-- `x` has tear free reads (§29.7.3): an aligned read event that cannot tear reads from at most
one write that cannot tear with its memory range (step 1.a.ii.1); its Assert holds. -/
def TearFreeReads (rbf : Rbf E) : Prop :=
  ∀ r, inSdb x r → isRead x r → x.noTear r = true →
    M.isInt (M.div (x.byteIndex r) (x.elementSize r)) = true ∧
    ∀ w, readsFrom x rbf r w → x.noTear w = true →
      ¬ (rangesEqual x r w ∧ ∃ v, rangesEqual x v w ∧ x.noTear v = true ∧ w ≠ v ∧ readsFrom x rbf r v)

/-- `mo` is an is-memory-order-before of `x` (§29.7.4). -/
structure MemoryOrder (rbf : Rbf E) (hsw : Rel E) (mo : Rel E) : Prop where
  order : StrictPartialOrder mo
  total : ∀ a b, inEvents x a → inEvents x b → a ≠ b → mo a b ∨ mo b a
  dom : ∀ a b, mo a b → inEvents x a ∧ inEvents x b
  hb : ∀ a b, HB x rbf hsw a b → mo a b
  /-- no ~seq-cst~ write with equal memory range comes between a read and the write it reads -/
  sc : ∀ r w, readsFrom x rbf r w → ¬ ∃ v, inSdb x v ∧ isWrite x v ∧ x.order v = .seqCst ∧
    mo w v ∧ mo v r ∧
    ((SyncWith x rbf hsw w r ∧ rangesEqual x v r) ∨
      (HB x rbf hsw w r ∧ HB x rbf hsw v r ∧ x.order w = .seqCst ∧ rangesEqual x w v) ∨
      (HB x rbf hsw w r ∧ HB x rbf hsw w v ∧ x.order r = .seqCst ∧ rangesEqual x v r))
  /-- a ~seq-cst~ write is memory-order after finitely many reads with its memory range -/
  finite : ∀ w, inSdb x w → isWrite x w → x.order w = .seqCst →
    ∃ l : List E, ∀ r, inSdb x r → isRead x r → rangesEqual x r w → mo r w → r ∈ l

/-- `x` has sequentially consistent atomics (§29.7.4): it admits an is-memory-order-before. -/
def SeqCstAtomics (rbf : Rbf E) (hsw : Rel E) : Prop := ∃ mo, MemoryOrder x rbf hsw mo

/-- `x` is a valid execution (§29.7.5) with the host's host-synchronizes-with `hsw` and the
reads-bytes-from function `rbf`. -/
structure ValidWith (rbf : Rbf E) (hsw : Rel E) : Prop where
  hostSync : HostSync x hsw
  readsBytesFrom : Rbf.Valid x rbf
  happensBefore : StrictPartialOrder (HB x rbf hsw)
  validChosenReads : ValidChosenReads x rbf
  coherentReads : CoherentReads x rbf hsw
  tearFreeReads : TearFreeReads x rbf
  seqCstAtomics : SeqCstAtomics x rbf hsw

/-- `x` is a valid execution (§29.7.5) with the host's host-synchronizes-with `hsw`: it admits a
reads-bytes-from function with which it is one. -/
def Valid (hsw : Rel E) : Prop := ∃ rbf, ValidWith x rbf hsw

/-- `a` and `b` are in a race (§29.8; InRace): distinct, not both happens-before each other
(RacesNotBoth, literal), and two writes whose ranges are not disjoint or one reading from the other. -/
def Race (rbf : Rbf E) (hsw : Rel E) (a b : E) : Prop :=
  a ≠ b ∧ ¬ (HB x rbf hsw a b ∧ HB x rbf hsw b a) ∧
    ((isWrite x a ∧ isWrite x b ∧ ¬ rangesDisjoint x a b) ∨ readsFrom x rbf a b ∨ readsFrom x rbf b a)

/-- `a` and `b` are in a data race (§29.9): in a race, and not both ~seq-cst~ or overlapping. -/
def DataRace (rbf : Rbf E) (hsw : Rel E) (a b : E) : Prop :=
  Race x rbf hsw a b ∧ (x.order a ≠ .seqCst ∨ x.order b ≠ .seqCst ∨ rangesOverlapping x a b)

/-- `x` is data race free (§29.10): no two of its Shared Data Block events are in a data race. -/
def DataRaceFree (rbf : Rbf E) (hsw : Rel E) : Prop :=
  ∀ a b, inSdb x a → inSdb x b → ¬ DataRace x rbf hsw a b

end Ecma.MemoryModel
