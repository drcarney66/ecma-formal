module

public import Ecma.Ops.ProgPrim
public import Ecma.Machine.Run
public import Ecma.Model.Laws
public import Ecma.Host.DateParse
public import Ecma.Gen.Decls

@[expose] public section

/-!
# What the host's laws are stated over

A host's answer (`Host.answers`, `Host.asks`), a host step (`Host.Step`), and the readings of the state the laws
share: Completion Records' kinds, Records by sort, the execution context stack, Strings as code units, and the
agent and elapsed-time helpers.
-/

namespace Ecma

/-- A HostSelectAgent answer that selects an agent. -/
def selects {M : Model} : Val M → Bool
  | .ref _ => true
  | _ => false

/-- The mathematical value of a finite or zero Number; `none` for ±∞𝔽 and *NaN*. -/
def numValue {M : Model} (n : M.Num) : Option M.Math :=
  match M.numView n with
  | .posZero | .negZero => some (M.ofNat 0)
  | .finite m => some m
  | _ => none

/-- The elapsed time the newest `next` of the log logged; 0 where there is none. -/
def lastElapsed {M : Model} : List (HostCall M) → M.Math
  | [] => M.ofNat 0
  | .next _ t :: _ => t
  | _ :: log => lastElapsed log

/-- `t₁` ≥ `t₀` + ℝ(`ms`): never for `ms` +∞, always for `ms` −∞ or *NaN*. -/
def mathAfter {M : Model} (t₀ t₁ : M.Math) (ms : M.Num) : Bool :=
  match numValue ms with
  | some m => !M.lt t₁ (M.add t₀ m)
  | none => match M.numView ms with
    | .posInf => false
    | _ => true

/-- A field of the Record a value refers to. -/
def fieldOf {M : Model} (s : State M) (f : FieldId) : Val M → Option (Val M)
  | .ref a => match M.heapGet s.heap a with
    | some (.record _ fs) => M.recGet fs f
    | _ => none
  | _ => none

/-- An internal slot of the object at `a`. -/
def slotOf {M : Model} (s : State M) (a : M.Addr) (f : FieldId) : Option (Val M) :=
  match M.heapGet s.heap a with
  | some (.object sl _) => M.recGet sl f
  | _ => none

/-- The elements of the List a value refers to. -/
def listElems {M : Model} (s : State M) : Val M → Option (List (Val M))
  | .ref a => match M.heapGet s.heap a with
    | some (.list xs _) => some (M.seqFoldl (fun l v => l ++ [v]) [] xs)
    | _ => none
  | _ => none

/-- A logged HostSelectAgent that selected an agent: the surrounding agent it was called in. -/
def HostCall.switchFrom {M : Model} : HostCall M → Option (Val M)
  | .choice q (a :: _) (.ref _) => if q == Known.pHostSelectAgent then some a else none
  | _ => none

/-- The log (newest first), each call with the agent it ran in: `cur` after the newest switch, a
switch's surrounding agent at it and before it. -/
def withAgents {M : Model} (cur : Val M) : List (HostCall M) → List (HostCall M × Val M)
  | [] => []
  | e :: log => let a := e.switchFrom.getD cur; (e, a) :: withAgents a log

/-- An Agent Record's signifier, its [[Signifier]]. -/
def sigOf {M : Model} (s : State M) (x : Val M) : Val M := (fieldOf s Known.fSignifier x).getD .absent

/-- ~empty~. -/
def isEmptyV {M : Model} : Val M → Bool
  | .enum e => e == Known.eEmpty
  | _ => false

/-- The waiter list of the agent `x`'s pending suspension (signifier `sig`) in a log with agents. -/
def pendingList {M : Model} (x sig : Val M) : List (HostCall M × Val M) → Option (Val M)
  | [] => none
  | (.choice q vs _, a) :: es =>
    if q == Known.pWakeAgent && vs.any (Val.same sig) then none
    else if q == Known.pSuspendAgentUntil && Val.same a x then vs.head?
    else pendingList x sig es
  | _ :: es => pendingList x sig es

/-- The agent `x`'s pending suspension is the host's own wait for a message or a job: its waiter list
is ~empty~ (SuspendThisAgent's is a WaiterList). -/
def idleWait {M : Model} (s : State M) (x : Val M) : Bool :=
  ((pendingList x (sigOf s x) (withAgents s.agent s.hostLog)).map isEmptyV).getD false

/-- The signifier of the agent whose job a logged call `e`, run in the agent `a`, schedules: its
_realm_'s [[AgentSignifier]] (§9.5: "in the agent signified by _realm_.[[AgentSignifier]]"), else (a
promise job of no realm) `a`'s. -/
def jobAgentOf {M : Model} (s : State M) : HostCall M × Val M → Val M
  | (.hook _ (_ :: realm :: _) _ _ _, a) => (fieldOf s Known.fAgentSignifier realm).getD (sigOf s a)
  | (_, a) => sigOf s a

/-- The signifiers of the agents of the jobs the log's calls schedule, by log position. -/
def jobAgents {M : Model} (s : State M) : Array (Val M) :=
  ((withAgents s.agent s.hostLog).map (jobAgentOf s)).reverse.toArray

/-- The signifiers of the surrounding agent's cluster: its candidate execution's Agent Events
Records' [[AgentSignifier]]s. -/
def clusterSigs {M : Model} (s : State M) : List (Val M) :=
  match ((fieldOf s Known.fCandidateExecution s.agent).bind (fieldOf s Known.fEventsRecords)).bind (listElems s) with
  | some ers => ers.filterMap (fieldOf s Known.fAgentSignifier)
  | none => []

variable {M : Model}

/-- `r` is the host-defined operation `c`'s answer to `xs` in `s`, the state then `s'`; an escaping
completion is its answer. -/
def Host.answers (H : Host M) (c : ClauseId) (xs : List (Val M)) (s : State M) (r : Val M) (s' : State M) : Prop :=
  Run.boundary (H.hook c xs) s = .ok r s'

/-- The host answers the question `q` without changing the state, and its answer has `P`. -/
def Host.asks (H : Host M) (q : PrimId) (P : List (Val M) → State M → Val M → Prop) : Prop :=
  ∀ vs s r s', H.choice q vs s = .ok r s' → s' = s ∧ P vs s r

/-- A host step from `s` to `s'`: a host-defined operation's or a host choice's answer, the next job,
whether to clear kept objects, a job's preparation or cleanup, the host's own first Job, what it does when
the agent has no Job, and its cleanup after either. -/
def Host.Step (H : Host M) (s s' : State M) : Prop :=
  (∃ c xs r, H.answers c xs s r s') ∨ (∃ q vs r, Run.boundary (H.choice q vs) s = .ok r s') ∨
    (∃ k, H.nextJob s = .ok k s') ∨ (∃ b, H.clearsKept s = .ok b s') ∨
    (∃ k, H.prepareJob k s = .ok () s') ∨ (∃ k, H.cleanupJob k s = .ok () s') ∨
    (∃ a, H.first s = .ok a s') ∨ (∃ a, H.idle s = .ok a s') ∨ ∃ v b, H.idleEnd v s = .ok b s'

/-- A Completion Record's [[Type]]; a value that is no Completion Record is a normal completion's. -/
def compType : Val M → EnumId
  | .comp t _ _ => t
  | _ => Known.eNormal

/-- The value of a normal completion; a value that is no Completion Record is its own. -/
def normalValue : Val M → Option (Val M)
  | .comp t v _ => if t == Known.eNormal then some v else none
  | v => some v

/-- `k` is the sort `t` or a subsort of it, by the data's `SortDef.super` (to depth `f`). -/
def dataSubSort : Nat → SortId → SortId → Bool
  | 0, k, t => k == t
  | f + 1, k, t => k == t || (((Gen.sortDefs[k]?).join.map (·.super)).getD []).any (dataSubSort f · t)

/-- A value is a Record of the sort named `sort`, or of a subsort of it. -/
def isRecordOf (s : State M) (sort : String) : Val M → Bool
  | .ref a => match M.heapGet s.heap a, Gen.sorts.idxOf? sort with
    | some (.record k _), some t => dataSubSort 64 k t
    | _, _ => false
  | _ => false

/-- A field id by its name in the data. -/
def fieldNamed (f : String) : FieldId := (Gen.fields.idxOf? f).getD 0

/-- The execution context stack as a List, the topmost last. -/
def stackList (s : State M) : List (Val M) := M.seqFoldl (fun l v => l ++ [v]) [] s.stack

/-- The elements of the List a value refers to. -/
def listAt (s : State M) : Val M → Option (List (Val M))
  | .ref a => match M.heapGet s.heap a with
    | some (.list sq _) => some (seqList sq)
    | _ => none
  | _ => none

/-- The code units `us` are the naturals `l`. -/
def unitsMatch : List M.Math → List Nat → Prop
  | [], [] => True
  | u :: us, c :: l => M.eq u (M.ofNat c) = true ∧ unitsMatch us l
  | _, _ => False

/-- The String `x`'s code units are `l`. -/
def unitsAre (x : M.Str) (l : List Nat) : Prop := unitsMatch (seqList (M.strUnits x)) l

end Ecma
