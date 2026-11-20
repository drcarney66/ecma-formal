module

public import Ecma.Host.Laws.Basic

@[expose] public section

/-!
# The laws of what a host step may change

The objects' invariants, the agent's fixed fields, the Realm's global object and its properties, extensions,
execution contexts, the FinalizationRegistry cleanup, tail calls' resources, and collection.
-/

namespace Ecma

variable {M : Model}

/-- The log has a DiscardContextResources choice for the execution context `ctx`. -/
def discardedIn (log : List (HostCall M)) : Val M → Bool
  | .ref a => log.any fun
    | .choice q [.ref b] _ => q == Known.pDiscardContextResources && M.addrEq a b
    | _ => false
  | _ => false

/-- The execution contexts on the stack whose resources no DiscardContextResources choice discarded. -/
def liveContexts (s : State M) : Nat := (stackList s).countP (!discardedIn s.hostLog ·)

/-- `s'` is `s` but for its heap, where every cell but `g`'s is as it was and `g` keeps its internal
slots: only `g`'s own properties change, and new cells may be allocated. -/
def onlyPropsOf (g : M.Addr) (s s' : State M) : Prop :=
  s' = { s with heap := s'.heap } ∧
  (∀ a c, a ≠ g → M.heapGet s.heap a = some c → M.heapGet s'.heap a = some c) ∧
  ∀ sl ps, M.heapGet s.heap g = some (.object sl ps) → ∃ ps', M.heapGet s'.heap g = some (.object sl ps')

/-- `s'` is `s` but for its heap, where only the objects `to` admits gain own properties: every other
cell is as it was, and such an object keeps its internal slots and the properties it had, and gains
none unless its [[Extensible]] is *true*; new cells may be allocated. -/
def onlyAdds (to : M.Addr → Prop) (s s' : State M) : Prop :=
  s' = { s with heap := s'.heap } ∧
  (∀ a c, M.heapGet s.heap a = some c → (∀ sl ps, to a → c ≠ .object sl ps) → M.heapGet s'.heap a = some c) ∧
  ∀ a sl ps, to a → M.heapGet s.heap a = some (.object sl ps) → ∃ ps', M.heapGet s'.heap a = some (.object sl ps') ∧
    (∀ k v, M.propsGet ps k = some v → M.propsGet ps' k = some v) ∧
    (M.recGet sl Known.fExtensible ≠ some (.bool true) → ∀ k, (M.propsGet ps' k).isSome → (M.propsGet ps k).isSome)

/-- The fields of the attribute Record that the property `k` of `ps` refers to in `s`. -/
def attrsAt (s : State M) (ps : M.Props (Val M)) (k : M.Str ⊕ M.Sym) : Option (M.Rec (Val M)) :=
  match M.propsGet ps k with
  | some (.ref p) => match M.heapGet s.heap p with
    | some (.record _ fs) => some fs
    | _ => none
  | _ => none

/-- §6.1.7.3 at a non-configurable property, from its attributes `fs` to `fs'`: every attribute but
[[Writable]] and [[Value]] is as it was; [[Writable]] is as it was or turns from *true* to *false*;
[[Value]] is as it was unless [[Writable]] was *true*. -/
def attrsKept (fs fs' : M.Rec (Val M)) : Prop :=
  (∀ f, f ≠ Known.fWritable → f ≠ Known.fValue → M.recGet fs' f = M.recGet fs f) ∧
  (M.recGet fs' Known.fWritable = M.recGet fs Known.fWritable ∨
    M.recGet fs Known.fWritable = some (.bool true) ∧ M.recGet fs' Known.fWritable = some (.bool false)) ∧
  (M.recGet fs Known.fWritable ≠ some (.bool true) → M.recGet fs' Known.fValue = M.recGet fs Known.fValue)

/-- sec-invariants-of-the-essential-internal-methods at an object, from slots `sl` and properties `ps` in `s` to
`sl'` and `ps'` in `s'`: [[Extensible]] is as it was or turns from *true* to *false*; an object whose
[[Extensible]] is not *true* keeps its [[Prototype]] and gains no property; a non-configurable property stays,
its attributes as `attrsKept` allows. -/
def objKept (s s' : State M) (sl : M.Rec (Val M)) (ps : M.Props (Val M)) (sl' : M.Rec (Val M))
    (ps' : M.Props (Val M)) : Prop :=
  (M.recGet sl' Known.fExtensible = M.recGet sl Known.fExtensible ∨
    M.recGet sl Known.fExtensible = some (.bool true) ∧ M.recGet sl' Known.fExtensible = some (.bool false)) ∧
  (M.recGet sl Known.fExtensible ≠ some (.bool true) → M.recGet sl' Known.fPrototype = M.recGet sl Known.fPrototype ∧
    ∀ k, (M.propsGet ps' k).isSome → (M.propsGet ps k).isSome) ∧
  ∀ k fs, attrsAt s ps k = some fs → M.recGet fs Known.fConfigurable ≠ some (.bool true) →
    ∃ fs', attrsAt s' ps' k = some fs' ∧ attrsKept fs fs'

/-- The components every execution context has (§9.4 Table 26), and those of an ECMAScript code
execution context (Table 27) and a generator's (Table 28). -/
def contextField (f : FieldId) : Prop :=
  f = Known.fCodeState ∨ f = Known.fFunction ∨ f = Known.fRealm ∨ f = Known.fScriptOrModule ∨
    f = Known.fLexicalEnvironment ∨ f = Known.fVariableEnvironment ∨ f = Known.fPrivateEnvironment ∨
    f = Known.fGenerator

/-- `a` is one of _realm_'s intrinsics in `s`: an object _realm_.[[Intrinsics]] holds, or one a property
of an intrinsic holds ([[Value]], [[Get]] or [[Set]]). Right after CreateIntrinsics(_realm_) these are
the objects it created (IntrinsicObjects: the well-known intrinsics and every object their
properties hold). -/
inductive intrinsicOf (s : State M) (realm : M.Addr) : M.Addr → Prop
  | named {k fs i k' is f a} : M.heapGet s.heap realm = some (.record k fs) →
      M.recGet fs Known.fIntrinsics = some (.ref i) → M.heapGet s.heap i = some (.record k' is) →
      M.recGet is f = some (.obj a) → intrinsicOf s realm a
  | held {o sl ps key p k fs f a} : intrinsicOf s realm o → M.heapGet s.heap o = some (.object sl ps) →
      M.propsGet ps key = some (.ref p) → M.heapGet s.heap p = some (.record k fs) →
      (f = Known.fValue ∨ f = Known.fGetter ∨ f = Known.fSetter) → M.recGet fs f = some (.obj a) →
      intrinsicOf s realm a

/-- §17.1: a function object (one with a [[Call]]) has an own *"caller"* or *"arguments"* property in
`s'` only if it had it in `s`. -/
def noForbiddenProps (s s' : State M) : Prop :=
  ∀ a sl ps' k, M.heapGet s'.heap a = some (.object sl ps') → (M.recGet sl Known.fCall).isSome →
    (M.strEq k (M.strLit "caller") = true ∨ M.strEq k (M.strLit "arguments") = true) →
    (M.propsGet ps' (.inl k)).isSome → ∃ ps, M.heapGet s.heap a = some (.object sl ps) ∧ (M.propsGet ps (.inl k)).isSome

/-- `c` is a Record that `reg`.[[Cells]] contains, whose [[WeakRefTarget]] is ~empty~. -/
def emptyCell (s : State M) (reg : Val M) (c : M.Addr) : Prop :=
  ∃ r sl ps l xs o i k fs, reg = .obj r ∧ M.heapGet s.heap r = some (.object sl ps) ∧
    M.recGet sl Known.fCells = some (.ref l) ∧ M.heapGet s.heap l = some (.list xs o) ∧
    M.seqGet xs i = some (.ref c) ∧ M.heapGet s.heap c = some (.record k fs) ∧
    M.recGet fs Known.fWeakRefTarget = some (.enum Known.eEmpty)

/-- The Agent Record fields whose values cannot change (§9.7: [[LittleEndian]], [[Signifier]],
[[IsLockFreeN]]) and [[GlobalSymbolRegistry]], which is never reassigned. -/
def agentFixedField (f : FieldId) : Prop :=
  f = fieldNamed "LittleEndian" ∨ f = fieldNamed "Signifier" ∨ f = fieldNamed "IsLockFree1" ∨
    f = fieldNamed "IsLockFree2" ∨ f = fieldNamed "IsLockFree8" ∨ f = fieldNamed "GlobalSymbolRegistry"

/-- From `s` to `s'`, the surrounding agent is the same, and its Agent Record keeps its sort and the
fields `agentFixedField` names. -/
def agentKept (s s' : State M) : Prop :=
  s'.agent = s.agent ∧ ∀ a k fs, s.agent = .ref a → M.heapGet s.heap a = some (.record k fs) →
    ∃ fs', M.heapGet s'.heap a = some (.record k fs') ∧ ∀ f, agentFixedField f → M.recGet fs' f = M.recGet fs f

/-! Collection (sec-weakref-execution). -/

/-- `v` is in the [[KeptAlive]] List of an agent's Agent Record in `s`. -/
def keptAlive (s : State M) (v : Val M) : Prop :=
  ∃ ag l xs, isRecordOf s "Agent Record" ag = true ∧ fieldOf s (fieldNamed "KeptAlive") ag = some l ∧
    listAt s l = some xs ∧ v ∈ xs

/-- `a` is a Record a WeakMap's [[WeakMapData]] List contains. -/
def weakMapEntry (s : State M) (a : M.Addr) : Prop :=
  ∃ o sl ps l es, M.heapGet s.heap o = some (.object sl ps) ∧ M.recGet sl (fieldNamed "WeakMapData") = some l ∧
    listAt s l = some es ∧ Val.ref a ∈ es

/-- `a` is the List a WeakSet's [[WeakSetData]] is. -/
def weakSetData (s : State M) (a : M.Addr) : Prop :=
  ∃ o sl ps, M.heapGet s.heap o = some (.object sl ps) ∧ M.recGet sl (fieldNamed "WeakSetData") = some (.ref a)

/-- `fs'` is `fs` with the fields `gs` set to ~empty~ where its field `k` is an element of `xs`, else `fs`. -/
def Rec.Emptied (xs : List (Val M)) (k : FieldId) (gs : List FieldId) (fs fs' : M.Rec (Val M)) : Prop :=
  (∃ v ∈ xs, M.recGet fs k = some v) ∧ fs' = gs.foldl (fun r g => M.recSet r g (.enum Known.eEmpty)) fs ∨
    (¬∃ v ∈ xs, M.recGet fs k = some v) ∧ fs' = fs

/-- The cell `c` at `a` becomes `c'` by sec-weakref-execution's steps for the set `xs`: a WeakRef's and a
FinalizationRegistry cell's [[WeakRefTarget]] in `xs` is set to ~empty~; a WeakMap entry whose [[Key]] is in
`xs` has its [[Key]] and [[Value]] set to ~empty~; a WeakSet's elements in `xs` are replaced by ~empty~; nothing
else changes. -/
def Cell.Emptied (s : State M) (xs : List (Val M)) (a : M.Addr) : Cell M → Cell M → Prop
  | .object sl ps, .object sl' ps' => ps' = ps ∧ Rec.Emptied xs Known.fWeakRefTarget [Known.fWeakRefTarget] sl sl'
  | .record k fs, .record k' fs' => k' = k ∧
      (weakMapEntry s a ∧ Rec.Emptied xs (fieldNamed "Key") [fieldNamed "Key", Known.fValue] fs fs' ∨
        ¬weakMapEntry s a ∧ Rec.Emptied xs Known.fWeakRefTarget [Known.fWeakRefTarget] fs fs')
  | .list ys o, .list ys' o' => o' = o ∧ (¬weakSetData s a → ys' = ys) ∧ M.seqLen ys' = M.seqLen ys ∧
      ∀ i v, M.seqGet ys i = some v →
        v ∈ xs ∧ M.seqGet ys' i = some (.enum Known.eEmpty) ∨ v ∉ xs ∧ M.seqGet ys' i = some v
  | c, c' => c' = c

/-- Values held directly by a continuation. -/
def Machine.Kont.Holds {M : Model} : Machine.Kont M → Val M → Prop
  | .args _ done _, v => v ∈ done
  | .all _ xs, v => v ∈ xs
  | .bind w, v => v = w
  | .scope (.passed outer inner), v => v ∈ outer ∨ v ∈ inner
  | .loop l, v | .test l, v => match l.st with
    | .each a _ _ | .keys a _ => v = .ref a
    | _ => False
  | .tstep _ _ _ key env _ _ _, v => v = key ∨ v ∈ env
  | _, _ => False

/-- Values directly in a suspended execution context's frame. -/
def Machine.Frame.Holds {M : Model} (fr : Machine.Frame M) (v : Val M) : Prop :=
  v ∈ fr.slots.toList ∨ ∃ k ∈ fr.konts, k.Holds v

/-- Subvalues referenced by a compound value. -/
def Val.Holds {M : Model} : Val M → Val M → Prop
  | .comp _ x y, v => v = x ∨ v = y
  | .clo _ caps, v => v ∈ caps
  | .ty _ _ _ env, v => v ∈ env
  | .cond _ _ _ _ env, v => v ∈ env
  | .tuple vs, v => v ∈ vs
  | _, _ => False

/-- §9.9.2 (`sec-liveness`): values strongly reachable from the roots of `s` without following
weak references (`WeakRef.[[WeakRefTarget]]`, `WeakSet.[[WeakSetData]]`, `WeakMap.[[WeakMapData]]`
entries whose `[[Key]]` is not itself reachable, or `FinalizationRegistry` cell `[[WeakRefTarget]]` /
`[[UnregisterToken]]` fields). -/
inductive Reachable (s : State M) : Val M → Prop
  | stack {v} : v ∈ stackList s → Reachable s v
  | resumed : Reachable s s.resumed
  | suspended : Reachable s s.suspended
  | agent : Reachable s s.agent
  | evalStep {p} : p ∈ s.evalSteps → Reachable s p.2
  | passed {v} : v ∈ s.passed → Reachable s v
  | waiterBlock {b i w} : (b, i, w) ∈ s.waiterLists → Reachable s (.ref b)
  | waiterRec {b i w} : (b, i, w) ∈ s.waiterLists → Reachable s (.ref w)
  | critical {w} : w ∈ s.critical → Reachable s (.ref w)
  | shared {b} : b ∈ s.shared → Reachable s (.ref b)
  | frame {ctx frs fr v} : (ctx, frs) ∈ s.frames → Reachable s (.ref ctx) →
      fr ∈ frs → fr.Holds v → Reachable s v
  | val {u v} : Reachable s u → u.Holds v → Reachable s v
  | objSlot {a sl ps f v} : Reachable s (.obj a) → M.heapGet s.heap a = some (.object sl ps) →
      f ≠ Known.fWeakRefTarget → f ≠ fieldNamed "WeakMapData" →
      f ≠ fieldNamed "WeakSetData" → f ≠ Known.fCells →
      M.recGet sl f = some v → Reachable s v
  | objKeySym {a sl ps sym u} : Reachable s (.obj a) → M.heapGet s.heap a = some (.object sl ps) →
      M.propsGet ps (.inr sym) = some u → Reachable s (.sym sym)
  | objProp {a sl ps k v} : Reachable s (.obj a) → M.heapGet s.heap a = some (.object sl ps) →
      M.propsGet ps k = some v → Reachable s v
  | finRegHeld {a sl ps l cs c k fs v} : Reachable s (.obj a) → M.heapGet s.heap a = some (.object sl ps) →
      M.recGet sl Known.fCells = some (.ref l) → listAt s (.ref l) = some cs →
      .ref c ∈ cs → M.heapGet s.heap c = some (.record k fs) →
      M.recGet fs (fieldNamed "HeldValue") = some v → Reachable s v
  | weakMapVal {a sl ps l es e ek fs k v} : Reachable s (.obj a) → M.heapGet s.heap a = some (.object sl ps) →
      M.recGet sl (fieldNamed "WeakMapData") = some (.ref l) → listAt s (.ref l) = some es →
      .ref e ∈ es → M.heapGet s.heap e = some (.record ek fs) →
      M.recGet fs (fieldNamed "Key") = some k → Reachable s k →
      M.recGet fs Known.fValue = some v → Reachable s v
  | recField {a k fs f v} : Reachable s (.ref a) → M.heapGet s.heap a = some (.record k fs) →
      M.recGet fs f = some v → Reachable s v
  | listElem {a xs o v} : Reachable s (.ref a) → M.heapGet s.heap a = some (.list xs o) →
      v ∈ seqList xs → Reachable s v
  | envField {a k fs b f v} : Reachable s (.ref a) → M.heapGet s.heap a = some (.env k fs b) →
      M.recGet fs f = some v → Reachable s v
  | envBind {a k fs b nm v} : Reachable s (.ref a) → M.heapGet s.heap a = some (.env k fs b) →
      M.propsGet b nm = some v → Reachable s v

/-- sec-weakref-execution: `s'` is `s` after the steps, performed atomically, for the set `xs` of objects and
Symbols, none of them in an agent's [[KeptAlive]] List or strongly reachable (`Reachable`)
(sec-liveness): every cell as `Cell.Emptied` says, every other component as it was. -/
def Collected (s : State M) (xs : List (Val M)) (s' : State M) : Prop :=
  (∀ x ∈ xs, ((∃ a, x = .obj a) ∨ ∃ y, x = .sym y) ∧ ¬keptAlive s x ∧ ¬Reachable s x) ∧
    s' = { s with heap := s'.heap } ∧
    ∀ a, (M.heapGet s'.heap a).isSome = (M.heapGet s.heap a).isSome ∧
      ∀ c, M.heapGet s.heap a = some c → ∃ c', M.heapGet s'.heap a = some c' ∧ Cell.Emptied s xs a c c'

/-- The laws of what a host step may change. -/
structure Host.ChangeLaws (H : Host M) : Prop where
  /-- sec-invariants-of-the-essential-internal-methods:
  "An implementation must not allow these invariants to be circumvented in any manner such as by providing alternative interfaces that implement the functionality of the essential internal methods without enforcing their invariants."
  Reading: across a host step every object is still an object and keeps to the invariants (`objKept`). -/
  invariantsKept : ∀ s s', H.Step s s' → ∀ a sl ps, M.heapGet s.heap a = some (.object sl ps) →
    ∃ sl' ps', M.heapGet s'.heap a = some (.object sl' ps') ∧ objKept s s' sl ps sl' ps'
  /-- sec-agents:
  "The values of [[LittleEndian]], [[Signifier]], [[IsLockFree1]], [[IsLockFree2]], and [[IsLockFree8]] cannot change."
  "The [[GlobalSymbolRegistry]] List is append-only and never reassigned."
  Reading: a host step keeps the surrounding agent, its Agent Record's sort and those fields (`agentKept`). -/
  agentFixed : ∀ s s', H.Step s s' → agentKept s s'
  /-- sec-initializehostdefinedrealm steps 10–10.a:
  "If the host requires use of a specific object to serve as realm's global object, then … Let global be such an object created in a host-defined manner."
  Reading: HostGlobalObject answers ~empty~ (the state as it was) or an Object. -/
  hostGlobalObject : ∀ vs s r s', H.choice Known.pHostGlobalObject vs s = .ok r s' →
    r = .enum Known.eEmpty ∧ s' = s ∨ ∃ a, r = .obj a
  /-- sec-initializehostdefinedrealm steps 12–12.a:
  "If the host requires that the this binding in realm's global scope return an object other than the global object, then … Let thisValue be such an object created in a host-defined manner."
  Reading: HostThisValue answers ~empty~ (the state as it was) or an Object. -/
  hostThisValue : ∀ vs s r s', H.choice Known.pHostThisValue vs s = .ok r s' →
    r = .enum Known.eEmpty ∧ s' = s ∨ ∃ a, r = .obj a
  /-- sec-initializehostdefinedrealm step 17:
  "Create any host-defined global object properties on global."
  Reading: HostGlobalProperties answers ~unused~ and changes only _global_'s own properties (`onlyPropsOf`). -/
  hostGlobalProperties : ∀ realm g s r s', H.choice Known.pHostGlobalProperties [realm, .obj g] s = .ok r s' →
    r = .enum Known.eUnused ∧ onlyPropsOf g s s'
  /-- sec-conformance:
  "a conforming implementation of ECMAScript may provide properties not described in this specification, and values for those properties, for objects that are described in this specification"
  sec-forbidden-extensions: "Built-in functions, strict functions created using the Function constructor, generator functions created using the Generator constructor, async functions created using the AsyncFunction constructor, and functions created using the bind method also must not be created with such own properties."
  Reading: HostExtendIntrinsics(_realm_) answers ~unused~ and only adds own properties to _realm_'s intrinsics
  (`intrinsicOf`), none to an object whose [[Extensible]] is not *true*, and no *"caller"* or *"arguments"* to a
  function. -/
  hostExtendIntrinsics : ∀ vs s r s', H.choice Known.pHostExtendIntrinsics vs s = .ok r s' →
    r = .enum Known.eUnused ∧ onlyAdds (fun a => ∃ realm, vs = [.ref realm] ∧ intrinsicOf s realm a) s s' ∧
      noForbiddenProps s s'
  /-- sec-conformance:
  "a conforming implementation of ECMAScript may provide properties not described in this specification, and values for those properties, for objects that are described in this specification"
  Reading: HostExtendObject(_o_) answers ~unused~ and only adds own properties to _o_, none if its [[Extensible]]
  is not *true*, and no *"caller"* or *"arguments"* to a function. -/
  hostExtendObject : ∀ o s r s', H.choice Known.pHostExtendObject [.obj o] s = .ok r s' →
    r = .enum Known.eUnused ∧ onlyAdds (· = o) s s' ∧ noForbiddenProps s s'
  /-- sec-builtincallorconstruct step 8:
  "Perform any necessary implementation-defined initialization of calleeContext."
  Reading: HostInitializeBuiltinContext answers ~unused~ and changes only _calleeContext_, which keeps its kind
  and every component the execution context tables define (`contextField`). -/
  hostInitializeBuiltinContext : ∀ ctx s r s', H.choice Known.pHostInitializeBuiltinContext [.ref ctx] s = .ok r s' →
    r = .enum Known.eUnused ∧ s' = { s with heap := s'.heap } ∧
      (∀ a c, a ≠ ctx → M.heapGet s.heap a = some c → M.heapGet s'.heap a = some c) ∧
      ∀ k fs, M.heapGet s.heap ctx = some (.record k fs) → ∃ fs', M.heapGet s'.heap ctx = some (.record k fs') ∧
        ∀ f, contextField f → M.recGet fs' f = M.recGet fs f
  /-- sec-host-cleanup-finalization-registry step 2:
  "If cleanupResult is an abrupt completion, perform any host-defined steps for reporting the error."
  Reading: HostReportCleanupError answers ~unused~. -/
  hostReportCleanupError : ∀ vs s r s', H.choice Known.pHostReportCleanupError vs s = .ok r s' →
    r = .enum Known.eUnused
  /-- No sentence: HostReportErrors is HTML's report-an-exception hook called by the readings overlay on an
  abrupt settle result of a PromiseReactionJob.
  Reading: HostReportErrors answers ~unused~. -/
  hostReportErrors : ∀ vs s r s', H.choice Known.pHostReportErrors vs s = .ok r s' →
    r = .enum Known.eUnused
  /-- sec-cleanup-finalization-registry step 3:
  "While finalizationRegistry.[[Cells]] contains a Record cell such that cell.[[WeakRefTarget]] is empty, an implementation may perform the following steps: 1. Choose any such cell."
  Reading: MayCleanup answers ~empty~ or such a cell (`emptyCell`), the state as it was. -/
  mayCleanup : ∀ reg s r s', H.choice Known.pMayCleanup [reg] s = .ok r s' →
    s' = s ∧ (r = .enum Known.eEmpty ∨ ∃ c, r = .ref c ∧ emptyCell s reg c)
  /-- sec-preparefortailcall step 2:
  "Discard all resources associated with the current execution context."
  Reading: DiscardContextResources answers ~unused~, the state as it was. -/
  discardContextResources : H.asks Known.pDiscardContextResources fun _ _ r => r = .enum Known.eUnused
  /-- sec-preparefortailcall:
  "A tail position call must either release any transient internal resources associated with the currently executing function execution context before invoking the target function or reuse those resources in support of the target function."
  Reading: the host's resources run out at a push onto the execution context stack (`Host.exhausts`) only while
  some context on it holds resources no DiscardContextResources discarded (`liveContexts`). -/
  contextResources : ∀ s, H.exhausts s = true → 0 < liveContexts s
  /-- sec-weakref-execution:
  "At any time, if a set of objects and/or symbols objSet is not live, an ECMAScript implementation may perform the following steps atomically"
  sec-liveness: "Any element in objSet is included in any agent's [[KeptAlive]] List."
  Reading: the host's collection empties, together, the WeakRefs, FinalizationRegistry cells, WeakMap entries and
  WeakSet elements of a set of objects and Symbols none of which is kept alive, and changes nothing else
  (`Collected`); a host that collects nothing meets it. -/
  collect : ∀ s xs s', H.collect s = .ok xs s' → Collected s xs s'

end Ecma
