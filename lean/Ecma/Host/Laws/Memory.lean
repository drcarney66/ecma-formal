module

public import Ecma.Host.Laws.Basic
public import Ecma.MemoryModel.View
public import Ecma.MemoryModel.Read

@[expose] public section

/-!
# The laws of shared memory and buffers

NaN encodings, Data Blocks, HostResizeArrayBuffer, and the bytes a shared read takes (sec-numerictorawbytes,
sec-createbytedatablock, sec-hostresizearraybuffer, sec-memory-model). The memory model's validity
(`Ecma.MemoryModel`) is read by `chooseReadsValid` alone.
-/

namespace Ecma

/-- HostSelectAgent's _agent_ and _n_. -/
def cutArgs {M : Model} : List (Val M) → Option (Val M × M.Math)
  | [a, n] => match n with
    | .math n => some (a, n)
    | _ => none
  | _ => none

/-- A logged HostSelectAgent that selected an agent: the agent it was called in and the number of
events of its [[EventList]] it gave. -/
def HostCall.cutOf {M : Model} : HostCall M → Option (Val M × M.Math)
  | .choice q vs r => if q == Known.pHostSelectAgent && selects r then cutArgs vs else none
  | _ => none

/-- The switches of a log (newest first), oldest first. -/
def cutsOf {M : Model} (log : List (HostCall M)) : List (Val M × M.Math) := log.reverse.filterMap HostCall.cutOf

/-- The place in the interleaving order of event `i` of the [[EventList]] of the agent whose signifier
is `sig`: the first of the switches `cuts` away from that agent after the event (past all of them where
there is none), then `i`. -/
def eventPlace {M : Model} (s : State M) (cuts : List (Val M × M.Math)) (sig : Val M) (i : Nat) : Nat × Nat :=
  ((cuts.findIdx? fun c => Val.same (sigOf s c.1) sig && M.lt (M.ofNat i) c.2).getD cuts.length, i)

/-- The place `p` is not after `q`. -/
def placeLe (p q : Nat × Nat) : Bool := p.1 < q.1 || p.1 == q.1 && p.2 ≤ q.2

/-- The events `es` from position `i`, each with its place `f`. -/
def placed {M : Model} (f : Nat → Nat × Nat) : Nat → List (Val M) → List (Val M × (Nat × Nat))
  | _, [] => []
  | i, e :: es => (e, f i) :: placed f (i + 1) es

/-- The elements of the List in field `f` of the Record `v`; none where there is none. -/
def fieldElems {M : Model} (s : State M) (f : FieldId) (v : Val M) : List (Val M) :=
  ((fieldOf s f v).bind (listElems s)).getD []

/-- The events of the candidate execution `ex`: its Agent Events Records' [[EventList]]s. -/
def execEvents {M : Model} (s : State M) (ex : Val M) : List (Val M) :=
  (fieldElems s Known.fEventsRecords ex).flatMap (fieldElems s Known.fEventList)

/-- The events of `ex`, each with its place in the interleaving order of the switches `cuts`. -/
def placedEvents {M : Model} (s : State M) (cuts : List (Val M × M.Math)) (ex : Val M) : List (Val M × (Nat × Nat)) :=
  (fieldElems s Known.fEventsRecords ex).flatMap fun er =>
    placed (eventPlace s cuts ((fieldOf s Known.fAgentSignifier er).getD .absent)) 0 (fieldElems s Known.fEventList er)

/-- The mathematical value in field `f` of the Record `v`; none where there is none. -/
def mathField {M : Model} (s : State M) (f : FieldId) (v : Val M) : Option M.Math :=
  match fieldOf s f v with
  | some (.math x) => some x
  | _ => none

/-- `e` is a write event (`isWrite`) whose [[Block]] is `block` and whose memory range contains `loc`. -/
def writesByte {M : Model} (isWrite : State M → Val M → Bool) (s : State M) (block : Val M) (loc : M.Math)
    (e : Val M) : Bool :=
  isWrite s e && (fieldOf s Known.fBlock e).any (Val.same · block) &&
    match mathField s Known.fByteIndex e, mathField s Known.fElementSize e with
    | some i, some k => !M.lt loc i && M.lt loc (M.add i k)
    | _, _ => false

variable {M : Model}

/-- A natural number is a NaN's encoding in the IEEE 754-2019 binary interchange format of `w`
exponent bits and precision `p`: `w + p` bits (the sign free), the biased exponent all ones and the
trailing significand not zero. -/
def nanBits (w p k : Nat) : Prop :=
  k < 2 ^ (w + p) ∧ (k / 2 ^ (p - 1)) % 2 ^ w = 2 ^ w - 1 ∧ k % 2 ^ (p - 1) ≠ 0

/-- A WriteSharedMemory or ReadModifyWriteSharedMemory event. -/
def isWriteEvent (s : State M) (e : Val M) : Bool :=
  isRecordOf s "WriteSharedMemory" e || isRecordOf s "ReadModifyWriteSharedMemory" e

/-- The memory model's names: Data's fields, enums and sorts. -/
def memNames : MemoryModel.View.Names := ⟨Gen.fields.idxOf?, Gen.enums.idxOf?, Gen.sorts.idxOf?⟩

/-- `mo` orders the events of the candidate execution `ex` as the interleaving order of the log's
switches places them. -/
def interleaved (s : State M) (ex : Val M) (mo : MemoryModel.Rel M.Addr) : Prop :=
  ∀ a b pa pb, (.ref a, pa) ∈ placedEvents s (cutsOf s.hostLog) ex → (.ref b, pb) ∈ placedEvents s (cutsOf s.hostLog) ex →
    a ≠ b → placeLe pa pb = true → mo a b

/-- The laws of shared memory and buffers. -/
structure Host.MemoryLaws (H : Host M) : Prop where
  /-- sec-numerictorawbytes step 1:
  "An implementation must always choose the same encoding for each implementation distinguishable NaN value."
  Reading: for a NaN and a format with a trailing significand field (2 ≤ p), NaNEncoding answers one NaN bit
  pattern of the format in every state, the state as it was. -/
  nanEncoding : ∀ (v : M.Num) (w p : Nat), M.numView v = .nan → 2 ≤ p → ∃ k, nanBits w p k ∧
    ∀ s, H.choice Known.pNaNEncoding [.num v, .math (M.ofNat w), .math (M.ofNat p)] s =
      .ok (.math (M.ofNat k)) s
  /-- sec-createbytedatablock step 2:
  "If it is impossible to create such a Data Block, throw a RangeError exception."
  Reading: CanAllocate, whether such a Data Block can be created, answers a Boolean, the state as it was. -/
  canAllocate : H.asks Known.pCanAllocate fun _ _ r => ∃ b, r = .bool b
  /-- sec-hostresizearraybuffer, the requirements:
  "The abstract operation does not detach buffer."
  "If the abstract operation completes normally with handled, buffer.[[ArrayBufferByteLength]] is newByteLength."
  Reading: _buffer_'s [[ArrayBufferData]] does not become *null*; on ~handled~ its
  [[ArrayBufferByteLength]] is _newByteLength_. -/
  resizeArrayBuffer : ∀ c a n s r s', Gen.clauses[c]? = some "sec-hostresizearraybuffer" →
    H.answers c [.obj a, n] s r s' →
    (∀ f, Gen.fields[f]? = some "ArrayBufferData" → slotOf s a f ≠ some .null → slotOf s' a f ≠ some .null) ∧
    (∀ e, normalValue r = some (.enum e) → Gen.enums[e]? = some "handled" →
      ∀ f m, Gen.fields[f]? = some "ArrayBufferByteLength" → n = .math m →
        ∃ m', slotOf s' a f = some (.math m') ∧ M.eq m' m = true)
  /-- sec-sharedarraybuffer-constructor:
  "Whenever a host does not provide concurrent access to SharedArrayBuffers it may omit the "SharedArrayBuffer" property of the global object."
  Reading: OmitSharedArrayBuffer is one Boolean in every state, the state as it was. -/
  omitSharedArrayBuffer : ∃ b, H.asks Known.pOmitSharedArrayBuffer fun _ _ r => r = .bool b
  /-- sec-atomics.pause:
  "It has no observable behaviour other than timing."
  Reading: SpinWaitHint answers ~unused~, the state as it was. -/
  spinWaitHint : H.asks Known.pSpinWaitHint fun _ _ r => r = .enum Known.eUnused
  /-- sec-getrawbytesfromsharedblock step 6:
  "Let rawValue be a List of length elementSize whose elements are nondeterministically chosen byte values."
  Reading: ChooseReadsBytesFrom(_execution_, _eventsRecord_, _block_, _byteIndex_, _elementSize_) answers a new
  List of _elementSize_ events of _execution_, the one at index _i_ a write event on _block_ whose memory range
  contains _byteIndex_ + _i_; the state as it was but for the new List. -/
  chooseReadsBytesFrom : ∀ vs s r s', H.choice Known.pChooseReadsBytesFrom vs s = .ok r s' →
    ∃ ex er block idx size ws, vs = [ex, er, block, .math idx, .math size] ∧ listOf ws s = .ok r s' ∧
      M.eq (M.ofNat ws.length) size = true ∧
      ∀ j w, ws[j]? = some w → w ∈ execEvents s ex ∧ writesByte isWriteEvent s block (M.add idx (M.ofNat j)) w = true
  /-- sec-valid-executions:
  "A candidate execution execution is a valid execution (or simply an execution) if all of the following are true."
  Reading: where _execution_ is a valid execution whose memory order agrees with the interleaving order and whose
  Shared Data Block events are formed, it stays one with the read appended to _eventsRecord_, reading the chosen
  events. -/
  chooseReadsValid : ∀ vs s r s', H.choice Known.pChooseReadsBytesFrom vs s = .ok r s' →
    ∀ ex er b idx size, vs = [ex, er, .ref b, .math idx, .math size] →
    ∃ ws : List M.Addr, listOf (ws.map .ref) s = .ok r s' ∧
      ∀ (d : CloSite → List (Val M) → List (Val M) → Run M (Val M)) rbf hsw mo k (ev : MemoryModel.NewEvent M),
        let x := MemoryModel.View.exec memNames d s ex
        MemoryModel.ValidWith x rbf hsw → MemoryModel.MemoryOrder x rbf hsw mo → interleaved s ex mo →
        MemoryModel.View.Formed memNames d s ex → x.records[k]? = some (MemoryModel.View.eventsRecord memNames s er) →
        ev.IsRead → ev.block = b → ev.byteIndex = idx → ev.elementSize = size → (∃ m, size = M.ofNat m) →
        MemoryModel.ReadsValid x rbf hsw k ev ws

end Ecma
