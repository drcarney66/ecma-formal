module

public import Ecma.Ops.Prim

@[expose] public section

/-!
# Leaf operations

What one transition of the machine does to values: reading a child of a Parse Node, sameness, indexing, making a
Record, the tests of the built-in types, and `Return`'s conversion to a Completion Record.
-/

namespace Ecma

variable {M : Model}

section Forms
variable (D : LeafCtx M) {n : Nat}

/-- An expression, evaluated: a computation in an environment. -/
abbrev EM (M : Model) (n : Nat) := Env M n → Run M (Val M)
/-- A variable's value; one not yet bound stops. -/
def Val.read : Val M → Run M (Val M)
  | .unbound => Run.stop .sortError
  | v => Run.pure v

/-- A bound-variable hole's value, the phrase to bind it: one not yet bound is `.absent`. -/
def Val.binder : Val M → Val M
  | .unbound => .absent
  | v => v

def evConst (v : Run M (Val M)) : EM M n := fun _ => v

/-- A datum's value. -/
def DataLit.val : DataLit → Val M
  | .sort s => .sort s
  | .choice i => .choice i
  | .absent => .absent

def evMath (sg : Sign) (m : Mag) : Val M :=
  match m with
  | .inf => if sg == .minus then .negInf else .posInf
  | _ => mathOf sg m

/-- An occurrence of a nonterminal at an SDO row's Parse Node, by its written position:
`the first |X|` … (k 0–2), `the fourth |X|` (7), `the derived |X|` (3: the right-hand side's X where X is also the
left-hand side), `the |X|` (4), `|X|` (5), the left-hand side's `|X|` (6, the node itself); an
optional item that is absent is `.absent`, and so is a `|X|` or `the |X|` the node's production
lacks (another production of the row has it: the generator's `row_children` check). -/
def childAt (k : Nat) (nt : NtId) (nd : M.Node) : Run M (Val M) :=
  if k == 6 then Run.pure (.node nd)
  else match M.nodeChild nd nt (if k == 7 then 3 else if k ≥ 3 then 0 else k) with
    | some (some c) => Run.pure (.node c)
    | some none => Run.pure .absent
    | none => if k == 4 || k == 5 then Run.pure .absent else Run.stop .sortError

/-- A node and the nodes it derives through unit productions (to depth `f`). -/
def unitChain : Nat → M.Node → List M.Node
  | 0, nd => [nd]
  | f + 1, nd => nd :: match D.unit (M.nodeProd nd) with
    | some c => match M.nodeChild nd c 0 with
      | some (some ch) => unitChain f ch
      | _ => []
    | none => []

/-- The nodes `the |X| of nd` reads: `nd`'s unit chain, or `nd` alone under UnitChainChild's literal reading. -/
def childChain (nd : M.Node) : List M.Node :=
  if D.reading Known.erUnitChainChild == .literal then [nd] else unitChain D 64 nd

/-- `the |X| of nd`: the child `nt` of the first node of `childChain` whose production has one. -/
def nodeChildOf (nt : NtId) (nd : M.Node) : Run M (Val M) :=
  match (childChain D nd).findSome? (M.nodeChild · nt 0) with
  | some (some c) => Run.pure (.node c)
  | some none => Run.pure .absent
  | none => Run.stop .sortError

/-- `childAt` at the row's Parse Node; outside an SDO row, a sort error. -/
def evChild (node : Option M.Node) (k : Nat) (nt : NtId) : Run M (Val M) :=
  match node with
  | some nd => childAt k nt nd
  | none => Run.stop .sortError

/-- `Val.same`, with a Parse Node the same as a production when a node of its unit chain is an
instance of it (`the derived |UnaryExpression|` is `PrimaryExpression : IdentifierReference`), and
the same as a terminal (the token `false`) when its right-hand side is that terminal alone. -/
def sameIs (v w : Val M) : Bool :=
  match v, w with
  | .node n, .prod ps | .prod ps, .node n => (unitChain D 64 n).any (ps.contains <| M.nodeProd ·)
  | .node n, .term t | .term t, .node n =>
    D.terms (M.nodeProd n) == [(0, t)] && M.seqFoldl (fun _ _ => false) true (M.nodeKids n)
  | .leaf _ _ s, .term t | .term t, .leaf _ _ s => s == t
  | _, _ => Val.same v w

/-- `v is w₁ or w₂ …`: a List of code points compared with a String is the String of them (`codeKey`). -/
def isVals (neg nei : Bool) (v : Val M) (ws : List (Val M)) : Run M Bool := do
  if ws.any (Val.incomparable v) then Run.stop .sortError else
  let v ← if ws.any (· matches .str _) then Prims.Strings.codeKey v else Run.pure v
  let any := ws.any (sameIs D v)
  return neg != (if nei then !any else any)

/-- The child `nt` of the node `e` gives, through its unit chain. -/
def evChildOf (e : EM M n) (nt : NtId) : EM M n := fun ρ => do
  match ← e ρ with
  | .node nd => nodeChildOf D nt nd
  | _ => Run.stop .sortError

def evIndex (e i : EM M n) : EM M n := fun ρ => do
  match ← e ρ, ← i ρ with
  | .ref a, .math k => do
    match ← readCell a with
    | .list xs o => optOr .sortError (M.seqGet xs (M.sub k (M.ofNat o)))
    | .block bs => optOr .sortError ((M.bytesGet bs k).map Val.math)
    | _ => Run.stop .sortError
  | _, _ => Run.stop .sortError

/-- A Record literal: a Completion Record is a value; any other Record a new cell. -/
def evRecord (k : Option SortId) (fs : Env M n → Run M (List (FieldId × Val M))) : EM M n := fun ρ => do
  let vs ← fs ρ
  if k == some Known.sComp then
    Run.pure (.comp (match look Known.fType vs with | .enum t => t | _ => Known.eNormal)
      (look Known.fValue vs) (look Known.fTarget vs))
  else
    return .ref (← alloc (.record (k.getD Known.sRecord) (vs.foldl (fun r (f, v) => M.recSet r f v) M.recEmpty)))

/-- A predicate, evaluated: a test of the subject. -/
abbrev PM (M : Model) (n : Nat) := Env M n → Val M → Run M Bool

/-- A predicate's subject that is a variable: read as bound, so that `is present` sees a parameter
not passed. -/
def _root_.Ecma.Expr.slot? : Expr → Option Slot
  | .var x => some x
  | _ => none

/-- The sorts of a list of sort values. -/
def sortVals : List (Val M) → Option (List SortId)
  | [] => some []
  | .sort s :: xs => (sortVals xs).map (s :: ·)
  | _ => none

/-- NewRecord's modifiers and sort: a type value of a sort, or the sort and then its modifiers. -/
def tyArg : List (Val M) → Option (List SortId × SortId)
  | [.ty (.sort _ mods s _) ..] => some (mods, s)
  | .sort s :: m :: ms => (sortVals (m :: ms)).map (·, s)
  | _ => none

/-- `nd` is an instance of `k`, or derives one through unit productions (to depth `f`, beyond
every chain of the grammar). -/
def derivesUnit (k : NtId) : Nat → M.Node → Bool
  | 0, nd => M.nodeNt nd == k
  | f + 1, nd => M.nodeNt nd == k || match D.unit (M.nodeProd nd) with
    | some c => match M.nodeChild nd c 0 with
      | some (some ch) => derivesUnit k f ch
      | _ => false
    | none => false

/-- `a |X|`: a Parse Node that is an instance of X or derives one through unit productions only
(one nonterminal and no terminals: a `( Expression )` is not an instance of what its Expression
derives); a String whose code points, all of them, parse as X. -/
def tyNt (k : NtId) : PM M n := fun _ v => match v with
  | .node nd => return derivesUnit D k 64 nd
  | .str t => do
    let cx : ParseCx := ⟨← D.annexB, false, false, k == Grammar.NT.Module.ctorIdx⟩
    let st ← newParse cx
    match M.parse D.reading cx st (Prims.Strings.strPoints t) k [] with
    | some r => return r.isSome
    | none => Run.stop .residue
  | _ => return false

end Forms

/-- `Return v`: in an algorithm whose header declares a Completion Record, a value
that is not one is a normal completion (§5.2.3.4). -/
def retConv (rc : Bool) (v : Val M) : Val M :=
  match v with
  | .comp t x y => .comp t x y
  | v => if rc then .comp Known.eNormal v (.enum Known.eEmpty) else v

end Ecma
