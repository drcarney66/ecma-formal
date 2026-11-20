module

public import Ecma.Ops.ProgPrim

@[expose] public section

/-!
# EnumerateObjectProperties as a host strategy

The actions and history of ForInStep (`ForInAct`, `ForInEntry`, `forInHist`, `actRecord`), the
rules of EnumerateObjectProperties over the history (`ForInRules`, `ForInRun`), the state machine
of %ForInIteratorPrototype%.next (`CfiSt`, `cfiNext`, `CfiOk`), and the conditions under which its
replay applies (`cfiApplies`).
-/

namespace Ecma

variable {M : Model}

/-- An action of the enumeration: call [[OwnPropertyKeys]], [[GetOwnProperty]] or [[GetPrototypeOf]]
of an object, return a key, or end. -/
inductive ForInAct (M : Model) where
  | keys (o : M.Addr)
  | own (o : M.Addr) (k : Val M)
  | proto (o : M.Addr)
  | yield (k : M.Str)
  | done

/-- An action of the history with its result: the keys; *undefined* (`none`) or a Property
Descriptor and whether its [[Enumerable]] is *true*; the prototype, `none` for *null*. -/
inductive ForInEntry (M : Model) where
  | keys (o : M.Addr) (ks : List (Val M))
  | own (o : M.Addr) (k : Val M) (d : Option Bool)
  | proto (o : M.Addr) (p : Option M.Addr)
  | yield (k : M.Str)

/-- The action an entry made. -/
def ForInEntry.act : ForInEntry M → ForInAct M
  | .keys o _ => .keys o
  | .own o k _ => .own o k
  | .proto o _ => .proto o
  | .yield k => .yield k

/-- The fields of the Record a value refers to. -/
def recIn (s : State M) : Val M → Option (M.Rec (Val M))
  | .ref a => match M.heapGet s.heap a with
    | some (.record _ fs) => some fs
    | _ => none
  | _ => none

/-- The elements of the List a value refers to. -/
def listIn (s : State M) : Val M → Option (List (Val M))
  | .ref a => match M.heapGet s.heap a with
    | some (.list xs _) => some (M.seqFoldl (fun l v => l ++ [v]) [] xs)
    | _ => none
  | _ => none

/-- The action an action Record states. -/
def actIn (s : State M) (v : Val M) : Option (ForInAct M) := do
  let fs ← recIn s v
  match M.recGet fs Known.fKind, M.recGet fs Known.fObject, M.recGet fs Known.fKey with
  | some (.enum k), some (.obj o), _ =>
    if k == Known.eOwnPropertyKeys then some (.keys o)
    else if k == Known.eGetPrototypeOf then some (.proto o)
    else if k == Known.eGetOwnProperty then (M.recGet fs Known.fKey).map (.own o)
    else none
  | some (.enum k), _, some (.str x) => if k == Known.eYield then some (.yield x) else none
  | some (.enum k), _, _ => if k == Known.eDone then some .done else none
  | _, _, _ => none

/-- An entry of the history: a Record { [[Action]], [[Result]] }, its Lists' elements read by `rd`. -/
def entryInBy (rd : State M → Val M → Option (List (Val M))) (s : State M) (v : Val M) : Option (ForInEntry M) := do
  let fs ← recIn s v
  let a ← M.recGet fs Known.fAction
  let r ← M.recGet fs Known.fResult
  match ← actIn s a with
  | .keys o => (rd s r).map (.keys o)
  | .own o k => match r with
    | .undefined => some (.own o k none)
    | d => (recIn s d).map fun dfs => .own o k (some (M.recGet dfs Known.fEnumerable matches some (.bool true)))
  | .proto o => match r with
    | .obj p => some (.proto o (some p))
    | .null => some (.proto o none)
    | _ => none
  | .yield k => some (.yield k)
  | .done => none

/-- An entry of the history: a Record { [[Action]], [[Result]] }. -/
def entryIn (s : State M) (v : Val M) : Option (ForInEntry M) := entryInBy listIn s v

/-- The history ForInStep is given, as entries. -/
def forInHist (s : State M) (h : Val M) : Option (List (ForInEntry M)) :=
  (listIn s h).bind fun vs => vs.mapM (entryIn s)

/-- A new action Record { [[Kind]], [[Object]], [[Key]] }, ~empty~ where the action has none. -/
def actRecord (a : ForInAct M) : Run M (Val M) := do
  let (k, o, x) : EnumId × Val M × Val M := match a with
    | .keys o => (Known.eOwnPropertyKeys, .obj o, .enum Known.eEmpty)
    | .own o k => (Known.eGetOwnProperty, .obj o, k)
    | .proto o => (Known.eGetPrototypeOf, .obj o, .enum Known.eEmpty)
    | .yield k => (Known.eYield, .enum Known.eEmpty, .str k)
    | .done => (Known.eDone, .enum Known.eEmpty, .enum Known.eEmpty)
  return .ref (← alloc (.record Known.sRecord
    (M.recSet (M.recSet (M.recSet M.recEmpty Known.fKind (.enum k)) Known.fObject o) Known.fKey x)))

/-- A For-In Iterator's state: [[Object]] (`none` for *null*), [[ObjectWasVisited]],
[[VisitedKeys]], [[RemainingKeys]], and the key `next` returns before it continues. -/
structure CfiSt (M : Model) where
  cur : Option M.Addr
  was : Bool
  visited : List M.Str
  remaining : List M.Str
  pending : Option M.Str

/-- CreateForInIterator(_obj_). -/
def CfiSt.init (obj : M.Addr) : CfiSt M := ⟨some obj, false, [], [], none⟩

/-- The keys that are Strings. -/
def strKeys (ks : List (Val M)) : List M.Str := ks.filterMap fun | .str k => some k | _ => none

/-- [[RemainingKeys]] without its first keys that [[VisitedKeys]] contains. -/
def cfiSkip (vis : List M.Str) : List M.Str → List M.Str
  | [] => []
  | k :: r => if vis.any (M.strEq · k) then cfiSkip vis r else k :: r

/-- The next action of `next`. -/
def CfiSt.next (st : CfiSt M) : ForInAct M :=
  match st.pending, st.cur with
  | some k, _ => .yield k
  | none, none => .done
  | none, some o => if !st.was then .keys o else match cfiSkip st.visited st.remaining with
    | k :: _ => .own o (.str k)
    | [] => .proto o

/-- The state after an action and its result. -/
def CfiSt.step (st : CfiSt M) : ForInEntry M → CfiSt M
  | .keys _ ks => { st with was := true, remaining := st.remaining ++ strKeys ks }
  | .own _ _ d => match cfiSkip st.visited st.remaining with
    | k :: r => ⟨st.cur, st.was, if d.isSome then st.visited ++ [k] else st.visited, r,
        if d = some true then some k else none⟩
    | [] => st
  | .proto _ p => { st with cur := p, was := false, remaining := [] }
  | .yield _ => { st with pending := none }

/-- The action `next` makes after the entries `es`. -/
def cfiNext (obj : M.Addr) (es : List (ForInEntry M)) : ForInAct M :=
  (es.foldl CfiSt.step (CfiSt.init obj)).next

/-! The rules (§14.7.5.9 EnumerateObjectProperties), over the entries before an action. -/

/-- `o` is _obj_ or an object a [[GetPrototypeOf]] call gave: an object of _obj_'s prototype chain. -/
def chainObj (obj : M.Addr) (es : List (ForInEntry M)) (o : M.Addr) : Prop :=
  o = obj ∨ ∃ p, ForInEntry.proto p (some o) ∈ es

/-- A key is accounted for: returned, or a [[GetOwnProperty]] call for it gave *undefined* or a
property that is not enumerable. -/
def accounted (es : List (ForInEntry M)) (k : M.Str) : Prop :=
  ForInEntry.yield k ∈ es ∨ ∃ o d, ForInEntry.own o (.str k) d ∈ es ∧ d ≠ some true

/-- The rules an action obeys after the entries `es`. -/
def ForInRules (obj : M.Addr) (es : List (ForInEntry M)) : ForInAct M → Prop
  /- ¶2 s3–s4: the own property keys of _obj_ and of its prototypes, recursively, by [[OwnPropertyKeys]]. -/
  | .keys o => chainObj obj es o
  /- ¶2 s5: attributes by [[GetOwnProperty]], of a key [[OwnPropertyKeys]] gave. -/
  | .own o k => chainObj obj es o ∧ ∃ ks, ForInEntry.keys o ks ∈ es ∧ k ∈ ks
  /- ¶2 s1: prototypes, recursively. -/
  | .proto o => chainObj obj es o
  /- step 1, ¶1 s3: a String key of an enumerable property; ¶1 s5: one [[GetOwnProperty]] found;
     ¶1 s7: at most once; ¶2 s1–s2: a prototype's property is not processed if a property of that
     name was, enumerable or not. -/
  | .yield k => (∀ e ∈ es, e ≠ .yield k) ∧ ∃ (i : Nat) (o : M.Addr), es[i]? = some (.own o (.str k) (some true)) ∧
      chainObj obj es o ∧ (o ≠ obj → ∀ j < i, ∀ o' d, es[j]? = some (.own o' (.str k) (some d)) → o' = o)
  /- step 1: all the String-valued keys of enumerable properties of _obj_ and its prototypes: the
     chain is walked to *null*, every object's keys are obtained, and each String key is
     accounted for. -/
  | .done => (∃ o, chainObj obj es o ∧ ForInEntry.proto o none ∈ es) ∧
      (∀ o, chainObj obj es o → ∃ ks, ForInEntry.keys o ks ∈ es) ∧
      ∀ o ks k, ForInEntry.keys o ks ∈ es → Val.str k ∈ ks → accounted es k

/-- Every entry obeyed the rules after the entries before it. -/
def ForInRun (obj : M.Addr) (es : List (ForInEntry M)) : Prop :=
  ∀ (i : Nat) (h : i < es.length), ForInRules obj (es.take i) es[i].act

/-! The replay of %ForInIteratorPrototype%.next (§14.7.5.10.2.1). -/

/-- Each entry is the action `next` makes from the state before it. -/
def CfiOk : CfiSt M → List (ForInEntry M) → Prop
  | _, [] => True
  | st, e :: es => e.act = st.next ∧ CfiOk (st.step e) es

/-! The conditions of ¶3 under which the iterator behaves as CreateForInIterator(_obj_)'s. -/

/-- `o` is _obj_ or an object of its prototype chain, by the [[Prototype]] slots of `s`. -/
inductive InChain (s : State M) (obj : M.Addr) : M.Addr → Prop
  | self : InChain s obj obj
  | step {o p sl ps} : InChain s obj o → M.heapGet s.heap o = some (.object sl ps) →
      M.recGet sl Known.fPrototype = some (.obj p) → InChain s obj p

/-- The slots of a Proxy exotic object, a TypedArray and a module namespace exotic object. -/
def exoticSlots : List FieldId := [Known.fProxyHandler, Known.fTypedArrayName, Known.fExports]

/-- No object of _obj_'s prototype chain is a Proxy exotic object, TypedArray or module namespace
exotic object; the model's objects have no other internal methods than the specification's. -/
def plainChain (s : State M) (obj : M.Addr) : Prop :=
  ∀ o sl ps, InChain s obj o → M.heapGet s.heap o = some (.object sl ps) →
    ∀ f ∈ exoticSlots, M.recGet sl f = none

/-- No object of the chain changed shape since the enumeration's first ForInStep call (a property
added to _obj_ itself aside): for-in calls `next` right after EnumerateObjectProperties returns. -/
def shapeKept (s : State M) (obj : M.Addr) (h : Val M) : Prop :=
  ∀ c ∈ s.shapeLog, InChain s obj c.obj → (c.added = true ∧ c.obj = obj) ∨
    ∀ i ans, s.hostLog.reverse[i]? = some (.choice Known.pForInStep [.obj obj, h] ans) → c.stamp ≤ i

/-- ¶3's conditions hold, and every action so far was CreateForInIterator's. -/
def cfiApplies (s : State M) (obj : M.Addr) (h : Val M) (es : List (ForInEntry M)) : Prop :=
  plainChain s obj ∧ shapeKept s obj h ∧ CfiOk (CfiSt.init obj) es

end Ecma
