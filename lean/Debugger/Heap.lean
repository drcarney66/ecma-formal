module

public import Debugger.View

@[expose] public section

/-!
# The debugger's heap, state and diffs

Engine-neutral (docs/debugger/state.md §3, §6, §7), over `Ecma.State` with the adapter's
`Names`:

- a cell by its kind, for `variables`: a Record's sort, then its fields; a List's elements,
  paged; an object's internal slots, then its own properties in [[OwnPropertyKeys]] order, each
  with its attributes; an Environment Record's kind, fields and bindings, an uninitialized binding
  in its TDZ;
- a summary line per cell, for `specHeap`; the state beside the heap, for `specState`;
- the difference between two pauses' states (`Diff`): the cells new since the earlier one (the
  heap only grows, so an address range), at most `diffLimit` earlier cells that differ, and whether
  the execution context stack changed; and the slots of the frames that changed.

Cells are compared structurally, sharing first: a cell the run has not written since the earlier
pause is the same object in both heaps.
-/

namespace Debugger

open Ecma

/-! Structural equality. -/

namespace Same

unsafe def ptr {α : Type} (a b : α) : Bool := ptrAddrUnsafe a == ptrAddrUnsafe b

def strOf (s : F.Str) : Array UInt16 := s
def symOf (s : F.Sym) : Nat × Option (Array UInt16) := s
def numOf (x : F.Num) : BitVec 64 := Engine.Model.Num.bits x
def seqOf (xs : F.Seq (Val F)) : Array (Val F) := xs
def recOf (r : F.Rec (Val F)) : Array (Option (FieldId × Val F)) := Engine.Model.WMap.entries (K := FieldId) r
def propsOf (r : F.Props (Val F)) : Array (Option ((Array UInt16 ⊕ (Nat × Option (Array UInt16))) × Val F)) :=
  Engine.Model.WMap.entries (K := Array UInt16 ⊕ (Nat × Option (Array UInt16))) r

def node (a b : F.Node) : Bool :=
  match a, b with
  | .mk k lo hi p .., .mk k' lo' hi' p' .. => k == k' && lo == lo' && hi == hi' && p == p'

def optNode : Option F.Node → Option F.Node → Bool
  | none, none => true
  | some a, some b => node a b
  | _, _ => false

mutual
unsafe def val (a b : Val F) : Bool :=
  ptr a b || match a, b with
  | .absent, .absent | .missing, .missing | .undefined, .undefined | .null, .null
  | .posInf, .posInf | .negInf, .negInf | .unbound, .unbound => true
  | .bool x, .bool y => x == y
  | .str x, .str y => strOf x == strOf y
  | .sym x, .sym y => symOf x == symOf y
  | .num x, .num y => numOf x == numOf y
  | .big x, .big y => Show.bigText x == Show.bigText y
  | .obj x, .obj y => Show.addr x == Show.addr y
  | .ref x, .ref y => Show.addr x == Show.addr y
  | .math x, .math y => Show.math x == Show.math y
  | .enum x, .enum y => x == y
  | .comp t v g, .comp t' v' g' => t == t' && val v v' && val g g'
  | .clo s cs, .clo s' cs' => s == s' && vals cs cs'
  | .alg x, .alg y => x == y
  | .node x, .node y => node x y
  | .leaf x i t, .leaf y j u => node x y && i == j && t == u
  | .term x, .term y => x == y
  | .ty t a nd e, .ty t' a' nd' e' => ptr t t' && a == a' && optNode nd nd' && vals e e'
  | .cond c xs a nd e, .cond c' xs' a' nd' e' => ptr c c' && xs == xs' && a == a' && optNode nd nd' && vals e e'
  | .field x, .field y => x == y
  | .nt x as, .nt y bs => x == y && as == bs
  | .param x, .param y => x == y
  | .prod x, .prod y => x == y
  | .sort x, .sort y => x == y
  | .choice x, .choice y => x == y
  | .clause x, .clause y => x == y
  | .table x, .table y => x == y
  | _, _ => false

unsafe def vals : List (Val F) → List (Val F) → Bool
  | [], [] => true
  | x :: xs, y :: ys => val x y && vals xs ys
  | _, _ => false
end

unsafe def arr (xs ys : Array (Val F)) : Bool :=
  ptr xs ys || (xs.size == ys.size && (xs.zip ys).all fun (x, y) => val x y)

unsafe def entries {K : Type} [BEq K] (xs ys : Array (Option (K × Val F))) : Bool :=
  ptr xs ys || (xs.size == ys.size && (xs.zip ys).all fun
    | (none, none) => true
    | (some (k, x), some (k', y)) => k == k' && val x y
    | _ => false)

unsafe def cell (a b : Cell F) : Bool :=
  ptr a b || match a, b with
  | .record k fs, .record k' fs' => k == k' && entries (recOf fs) (recOf fs')
  | .list xs o, .list ys o' => o == o' && arr (seqOf xs) (seqOf ys)
  | .block bs, .block bs' => bs == bs'
  | .charSet cs, .charSet cs' => cs == cs'
  | .object sl ps, .object sl' ps' => entries (recOf sl) (recOf sl') && entries (propsOf ps) (propsOf ps')
  | .env k fs bs, .env k' fs' bs' => k == k' && entries (recOf fs) (recOf fs') && entries (propsOf bs) (propsOf bs')
  | _, _ => false

unsafe def valPtr (a b : Val F) : Bool := ptr a b

end Same

/-- Whether two cells are equal, structurally. -/
@[implemented_by Same.cell] opaque cellSame : Cell F → Cell F → Bool

/-- Whether two values are equal, structurally. -/
@[implemented_by Same.val] opaque valSame : Val F → Val F → Bool

/-- Whether two values are one object in memory: a value passed on, not made anew. -/
@[implemented_by Same.valPtr] opaque sameObject : Val F → Val F → Bool

/-! Diffs. -/

def heapOf (s : State F) : Array (Cell F) := s.heap

def stackOf (s : State F) : Array (Val F) := s.stack

/-- The changed cells a diff lists at most. -/
def diffLimit : Nat := 50

/-- Two pauses' states compared: the new cells `[lo, hi)`, the earlier cells that differ (at most
`diffLimit`, `truncated` if there are more) and whether the execution context stack differs. -/
structure Diff where
  lo : Nat
  hi : Nat
  changed : Array Nat
  truncated : Bool
  stackChanged : Bool

def diff (old new : State F) : Diff := Id.run do
  let h0 := heapOf old
  let h1 := heapOf new
  let mut changed := #[]
  let mut truncated := false
  for a in [0:min h0.size h1.size] do
    match h0[a]?, h1[a]? with
    | some x, some y =>
      if !cellSame x y then
        if changed.size == diffLimit then
          truncated := true
          break
        changed := changed.push a
    | _, _ => pure ()
  let s0 := stackOf old
  let s1 := stackOf new
  let stackChanged := s0.size != s1.size || (s0.zip s1).any fun (x, y) => !valSame x y
  return { lo := h0.size, hi := h1.size, changed, truncated, stackChanged }

def Diff.json (d : Diff) : Json :=
  Json.mk [("newCells", .arr #[.nat d.lo, .nat d.hi]), ("changed", .arr (d.changed.map Json.nat)),
    ("truncated", d.truncated), ("stackChanged", d.stackChanged)]

/-- Each frame's algorithm and slot values, outermost first: what the next pause compares with. -/
abbrev SlotsSeen := List (AlgId × List (Val F))

def slotsSeen (fs : List FrameView) : SlotsSeen := fs.reverse.map fun f => (f.alg, f.slots.map (·.2))

/-- For each frame (innermost first), the slots that differ from the previous pause's: frames
matched by position from the outermost one, and by algorithm. -/
def changedSlots (prev : SlotsSeen) (fs : List FrameView) : List (List Nat) :=
  (fs.reverse.zipIdx.map fun (f, i) => match prev[i]? with
    | some (a, vs) =>
      if a == f.alg then
        f.slots.zipIdx.filterMap fun ((_, v), j) => match vs[j]? with
          | some w => if valSame v w then none else some j
          | none => some j
      else []
    | none => []).reverse

/-! Cells by kind. -/

/-- A page of a List's elements: from `start`, at most `count` (all when none). -/
structure Page where
  start : Nat := 0
  count : Option Nat := none

def fieldVars (n : Names) (s : State F) (fs : F.Rec (Val F)) : List Var :=
  (F.recKeys fs).toList.filterMap fun f => (F.recGet fs f).map fun v => cellVar n s s!"[[{n.field f}]]" v

/-- A property key as a name: a String as its text, a Symbol as `[Symbol("d") #i]`. -/
def keyName (n : Names) (k : F.Str ⊕ F.Sym) : String :=
  match k with
  | .inl t => Show.text t
  | .inr y => "[" ++ Show.val n (.sym y) ++ "]"

/-- An array index (§6.1.7): a String that is a canonical integer below 2³² - 1. -/
def arrayIndex? (k : F.Str ⊕ F.Sym) : Option Nat :=
  match k with
  | .inl t =>
    let x := Show.text t
    match x.toNat? with
    | some i => if toString i == x && i < 2 ^ 32 - 1 then some i else none
    | none => none
  | .inr _ => none

/-- Own property keys in [[OwnPropertyKeys]] order (§10.1.11.1): array indices ascending, then
Strings, then Symbols, in creation order. -/
def ownKeys (ps : F.Props (Val F)) : List (F.Str ⊕ F.Sym) :=
  let ks := (F.propsKeys ps).toList
  let idx := ((ks.filterMap fun k => (arrayIndex? k).map (·, k)).toArray.qsort (·.1 < ·.1)).toList.map (·.2)
  let strs := ks.filter fun k => k.isLeft && (arrayIndex? k).isNone
  idx ++ strs ++ ks.filter (·.isRight)

def flagText (fs : F.Rec (Val F)) (f : FieldId) (yes no : String) : Option String :=
  match F.recGet fs f with
  | some (.bool true) => some yes
  | some (.bool false) => some no
  | _ => none

/-- An own property, its attribute Record `v`: its value (or getter and setter) and attributes;
it expands to the Record. -/
def propVar (n : Names) (s : State F) (name : String) (v : Val F) : Var :=
  match v with
  | .ref r => match cell? s (Show.addr r) with
    | some (.record _ fs) =>
      let flags := [flagText fs Known.fWritable "writable" "non-writable",
        flagText fs Known.fEnumerable "enumerable" "non-enumerable",
        flagText fs Known.fConfigurable "configurable" "non-configurable"].filterMap id
      let shown := fun f => ((F.recGet fs f).map (Show.val n)).getD "undefined"
      let (kind, value) := match F.recGet fs Known.fValue with
        | some x => ("data property", Show.val n x)
        | none => ("accessor property", s!"get {shown Known.fGet}, set {shown Known.fSet}")
      { name, value, type := s!"{kind} ({", ".intercalate flags})", ref := Show.ref v }
    | _ => cellVar n s name v
  | _ => cellVar n s name v

/-- A binding, its binding Record `v`: its value, or `TDZ` while uninitialized, an indirect one's
target; mutability, strictness and deletability as its type. It expands to the Record. -/
def bindVar (n : Names) (s : State F) (name : String) (v : Val F) : Var :=
  match v with
  | .ref r => match cell? s (Show.addr r) with
    | some (.record _ fs) =>
      let get := fun (x : String) => (n.fieldId x).bind (F.recGet fs ·)
      let isB := fun (x : String) (b : Bool) => match get x with
        | some (.bool c) => c == b
        | _ => false
      let tdz := isB "Initialized" false
      let words := [if isB "Mutable" true then "mutable" else "immutable"] ++
        (if isB "Strict" true then ["strict"] else []) ++ (if isB "Deletable" true then ["deletable"] else []) ++
        [if tdz then "uninitialized (TDZ)" else "initialized"]
      let value := if tdz then "TDZ" else match get "Module", get "BindingName" with
        | some m, some b => s!"indirect: {Show.val n b} of {Show.val n m}"
        | _, _ => ((F.recGet fs Known.fValue).map (Show.val n)).getD "?"
      { name, value, type := ", ".intercalate words, ref := Show.ref v }
    | _ => cellVar n s name v
  | _ => cellVar n s name v

/-- A cell's parts: a Record's sort, then its fields; an Environment Record's kind, fields and
bindings by name; an object's internal slots, then its own properties; a List's elements of the
page `pg`, numbered from its origin. -/
def cellVars (n : Names) (s : State F) (a : Nat) (pg : Page := {}) : Option (List Var) :=
  (cell? s a).map fun
    | .record k fs => { name := "sort", value := n.sort k, type := "sort" } :: fieldVars n s fs
    | .env k fs bs =>
      { name := "kind", value := n.sort k, type := "sort" } :: fieldVars n s fs ++
        (F.propsKeys bs).toList.filterMap fun k => (F.propsGet bs k).map (bindVar n s (keyName n k))
    | .object sl ps =>
      fieldVars n s sl ++ (ownKeys ps).filterMap fun k => (F.propsGet ps k).map (propVar n s (keyName n k))
    | .list xs origin =>
      let xs := Same.seqOf xs
      let hi := match pg.count with
        | some c => min xs.size (pg.start + c)
        | none => xs.size
      (List.range' pg.start (hi - pg.start)).filterMap fun i => xs[i]?.map (cellVar n s s!"[{i + origin}]")
    | .block bs =>
      let hi := match pg.count with
        | some c => min bs.size (pg.start + c)
        | none => bs.size
      (List.range' pg.start (hi - pg.start)).map fun i => cellVar n s s!"[{i}]" (.math (.int (bs.get! i).toNat))
    | .charSet cs =>
      let sz := (Engine.Model.MathVal.idx (F.csSize cs)).getD 0
      let hi := match pg.count with
        | some c => min sz (pg.start + c)
        | none => sz
      (List.range' pg.start (hi - pg.start)).filterMap fun i => (F.csGet cs (F.ofNat i)).map fun sq =>
        match sq.toList with
        | [c] => cellVar n s s!"[{i}]" (.math c)
        | cs' =>
          { name := s!"[{i}]"
            value := "«" ++ ", ".intercalate (cs'.map fun c => Show.valAt n false (.math c)) ++ "»"
            type := s!"List ({cs'.length})"
            ref := 0 }

/-- `vs` with the ones that differ from `old` (by name: value or type) marked `changed`. -/
def markChanged (old vs : List Var) : List Var :=
  vs.map fun v => match old.find? (·.name == v.name) with
    | some o => if o.value.render == v.value.render && o.type == v.type then v else { v with attrs := ["changed"] }
    | none => { v with attrs := ["changed"] }

/-! Summaries. -/

def cellKind : Cell F → String
  | .record .. => "record"
  | .list .. => "list"
  | .block .. => "block"
  | .charSet .. => "charset"
  | .object .. => "object"
  | .env .. => "env"

def cellTypeOf (n : Names) : Cell F → String
  | .record k _ | .env k _ _ => n.sort k
  | .list xs _ => s!"List ({xs.size})"
  | .block bs => s!"Data Block ({bs.size})"
  | .charSet cs => s!"CharSet ({(Engine.Model.MathVal.idx (F.csSize cs)).getD 0})"
  | .object .. => "Object"

/-- The first `k` of `xs`, joined, with `…` if there are more. -/
def preview (k : Nat) (xs : List String) : String :=
  ", ".intercalate (xs.take k) ++ (if xs.length > k then ", …" else "")

/-- A cell in one line: its kind, and its first fields, elements, properties or bindings. -/
def cellSummary (n : Names) : Cell F → String
  | .record k fs =>
    s!"{n.sort k} \{" ++ preview 3 ((F.recKeys fs).toList.filterMap fun f =>
      (F.recGet fs f).map fun v => s!"[[{n.field f}]]: {Show.valAt n false v}") ++ "}"
  | .list xs o =>
    s!"List ({xs.size}" ++ (if o == 0 then "" else s!", from {o}") ++ ") [" ++
      preview 5 ((Same.seqOf xs).toList.map (Show.valAt n false)) ++ "]"
  | .block bs =>
    let elems := (List.range (min bs.size 5)).map fun i => Show.valAt n false (.math (.int (bs.get! i).toNat))
    s!"Data Block ({bs.size}) [" ++ preview 5 elems ++ "]"
  | .charSet cs =>
    let sz := (Engine.Model.MathVal.idx (F.csSize cs)).getD 0
    let elems := (List.range (min sz 5)).filterMap fun i => (F.csGet cs (F.ofNat i)).map fun sq =>
      match sq.toList with
      | [c] => Show.valAt n false (.math c)
      | cs' => "«" ++ ", ".intercalate (cs'.map fun c => Show.valAt n false (.math c)) ++ "»"
    s!"CharSet ({sz}) \{" ++ preview 5 elems ++ "}"
  | .object sl ps =>
    s!"Object ({(F.recKeys sl).size} slots) \{" ++ preview 5 ((ownKeys ps).map (keyName n)) ++ "}"
  | .env k _ bs => s!"{n.sort k} \{" ++ preview 5 ((F.propsKeys bs).toList.map (keyName n)) ++ "}"

/-- The cells a `specHeap` response looks at most. -/
def heapLimit : Nat := 1000

/-- `specHeap`: the cells at `[lo, lo + count)` (`count` at most `heapLimit`) of kind `kind` (any if
none), and the heap's size. -/
def heapJson (n : Names) (s : State F) (lo count : Nat) (kind : Option String) : Json :=
  let h := heapOf s
  let hi := min h.size (lo + min count heapLimit)
  let cells := (List.range' lo (hi - lo)).filterMap fun a => h[a]?.bind fun c =>
    if kind.all (· == cellKind c) then
      some (Json.mk [("addr", .nat a), ("kind", cellKind c), ("type", cellTypeOf n c), ("summary", cellSummary n c),
        ("variablesReference", .nat (a + 1))])
    else none
  Json.mk [("cells", .arr cells.toArray), ("heapSize", .nat h.size)]

/-- `specDiff`: cell `a` at the previous pause (`old`, null if new since) and now (`new`), and the
names of its parts that differ. -/
def cellDiffJson (n : Names) (prev : Option (State F)) (s : State F) (a : Nat) : Except String Json :=
  let side := fun (st : State F) => (cell? st a).map fun c =>
    Json.mk [("kind", cellKind c), ("summary", cellSummary n c),
      ("variables", .arr (((cellVars n st a).getD []).map Var.json).toArray)]
  let old := prev.bind side
  let new := side s
  if new.isNone then .error s!"no cell #{a}" else
  let names : List String := match prev.bind (cellVars n · a), cellVars n s a with
    | some o, some nw =>
      ((markChanged o nw).filter fun (v : Var) => !v.attrs.isEmpty).map Var.name ++
        (o.filter fun (v : Var) => !nw.any fun (w : Var) => w.name == v.name).map Var.name
    | none, some nw => nw.map Var.name
    | _, _ => []
  .ok (Json.mk [("addr", .nat a), ("old", old.getD .null), ("new", new.getD .null),
    ("changed", .arr (names.map Json.str).toArray)])

/-! The state beside the heap. -/

/-- A parse's root: its stamp, production, span and how it was parsed. -/
def rootJson (n : Names) (s : State F) (nd : F.Node) : Json :=
  let .mk k lo hi p nt _ _ _ := nd
  let how := if s.jsonParses.contains k then "JSON" else if s.directParses.contains k then "direct eval"
    else if s.strictParses.contains k then "strict from outside" else "source"
  Json.mk [("parse", .nat k), ("production", Show.prodText n nt p), ("lo", .nat lo), ("hi", .nat hi), ("kind", how)]

/-- `specState`: the Agent Record, the Symbols and parses so far with each parse's root, the Parse
Nodes whose SDOs are running, the arguments Lists of the running built-in calls, and the "host /
model" group `host` (state.md §6). -/
def stateJson (n : Names) (s : State F) (host : List (String × Json)) : Json :=
  Json.mk [("agent", (cellVar n s "agent" s.agent).json), ("symbols", .nat s.syms), ("parses", .nat s.parses),
    -- latest first: stamps rise with insertion
    ("roots", .arr (s.roots.values.reverse.map (rootJson n s)).toArray),
    ("evalNodes", .arr (s.evalNodes.map fun nd => Json.str (Show.node n nd)).toArray),
    ("passed", .arr (s.passed.zipIdx.map fun (v, i) => (cellVar n s s!"[{i}]" v).json).toArray),
    ("contexts", .nat (stackOf s).size), ("heapSize", .nat (heapOf s).size),
    ("host", Json.mk (host ++ [("hostLog", .nat s.hostLog.length), ("shapeLog", .nat s.shapeLog.length)]))]

/-! `variables`. -/

/-- `variables` of reference `r` at the pause `p`: a scope's (the Slots that differ from the
previous pause's, `changed` per frame, marked), or a cell's page `pg` (its parts shown otherwise
than at the previous pause's state `prev` marked: an object's property whose attribute Record
changed too). -/
def variables (n : Names) (srcs : Sources) (p : Paused) (prev : Option (State F))
    (changed : List (List Nat)) (r : Nat) (pg : Page := {}) : Except String (List Var) :=
  match decodeRef r with
  | .inl none => .error s!"no such reference {r}"
  | .inl (some (id, k)) =>
    let frames := p.frames ()
    match frames[id]? with
    | none => .error s!"no frame {id}"
    | some f => match k with
      | .slots =>
        let ch := changed[id]?.getD []
        .ok ((slotVars n p.state f).zipIdx.map fun (v, j) => if ch.contains j then { v with attrs := ["changed"] } else v)
      | .step => .ok (stepVars f id)
      | .konts => .ok (kontVars f)
      | .node => match f.node with
        | some nd => .ok (nodeVars n srcs nd)
        | none => .error "the frame has no Parse Node"
      | .contexts => match p.state with
        | some s => .ok (contextVars n s frames)
        | none => .error "no state at a stop"
  | .inr a => match p.state with
    | some s => match cellVars n s a pg with
      | some vs => match prev.bind (cellVars n · a pg) with
        | some old => .ok (markChanged old vs)
        | none => .ok vs
      | none => .error s!"no cell #{a}"
    | none => .error "no state at a stop"

end Debugger
