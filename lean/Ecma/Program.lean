module

public import Ecma.Host.Jobs
public import Ecma.Ops.Unchecked
public import Ecma.Grammar.Print
public import Ecma.Prims.Realm

@[expose] public section

/-!
# The program

`Prog`: the specification's algorithms, SDO rows, productions, sorts, phrases, tables and early-error rules as
lookups, with what a header says of an algorithm (`Header.rc`, `Header.arity`) and membership in a sort
(`sortTest`).
-/

namespace Ecma

variable {M : Model}

/-- A condition that binds a variable in its consequent: a lone predicate phrase with a bound
variable hole (`contains a T x such that c`), whose value is the List of the values it binds. -/
def Cond.binder? : Cond → Option (Expr × PhraseId × List Hole × Slot)
  | .preds e (.phrase p hs) [] => (hs.findSome? fun | .b x => some x | _ => none).map (e, p, hs, ·)
  | _ => none

/-- A node's child nodes in order: its present right-hand side's symbols, a terminal's Parse Node at
its position and the nonterminals' nodes between. -/
def childVals (D : LeafCtx M) (nd : M.Node) : List (Val M) :=
  let ts := D.terms (M.nodeProd nd)
  let kids := (M.seqFoldl (fun acc c => c :: acc) [] (M.nodeKids nd)).reverse
  let rec go : Nat → Nat → List M.Node → List (Val M)
    | 0, _, _ => []
    | f + 1, i, ks => match ts.lookup i, ks with
      | some t, _ => .leaf nd i t :: go f (i + 1) ks
      | none, k :: ks => .node k :: go f (i + 1) ks
      | none, [] => []
  go (ts.length + kids.length) 0 kids

/-! Algorithms and the program. -/

/-- Whether an algorithm's header declares a Completion Record: internal methods, built-in
functions, and every header whose return type is a completion. -/
def Header.rc (h : Header) : Bool :=
  match h.kind, h.ret with
  | .internalMethod, _ => true
  | .builtin, _ => true
  | _, some t => isComp t || match t with
    | .union _ _ ts => ts.any isComp
    | _ => false
  | _, none => false
where
  isComp : TyExpr → Bool
    | .completion _ => true
    | .sort _ _ s _ => s == Known.sComp || s == Known.sNormalComp || s == Known.sAbruptComp ||
        s == Known.sThrowComp || s == Known.sReturnComp
    | _ => false

/-- The number of slots a call binds: the receiver and the parameters. -/
def Header.arity (h : Header) : Nat := h.params.length + (if h.recv.isSome then 1 else 0)


/-- §18: a call's arguments to `a`, as uses see them; a built-in function's as EvaluateBuiltin
binds them, a parameter not present (`.missing`, also past them) staying not present. -/
def Alg.args (a : Alg) (vs : List (Val M)) : List (Val M) :=
  if a.header.kind == .builtin then
    let n := (a.header.params.filter (!·.rest)).foldl (fun m p => max m (p.x + 1)) 0
    vs ++ List.replicate (n - vs.length) .missing
  else vs.map Val.used

/-- Whether an SDO's header, by `Decls.sdoHeaders`, declares a Completion Record. -/
def sdoRc (hs : Array (Option Header)) (s : SdoId) : Bool :=
  match hs[s]? with
  | some (some h) => h.rc
  | _ => false

/-- An SDO's number of parameters, by its header. -/
def sdoArity (hs : Array (Option Header)) (s : SdoId) : Nat :=
  match hs[s]? with
  | some (some h) => h.params.length
  | _ => 0

/-- What the knot resolves: the program's algorithms, SDO rows, chain productions, concrete
methods by Record kind, and phrase meanings. -/
structure Prog where
  alg : AlgId → Option Alg
  row : SdoId → ProdId → Option SdoRow
  /-- the sole nonterminal of a chain production -/
  chain : ProdId → Option NtId
  /-- the sole nonterminal of a unit production (no terminals) -/
  unit : ProdId → Option NtId
  /-- the terminals of a production's present right-hand side, by position -/
  terms : ProdId → List (Nat × String)
  /-- an SDO's default definition, for the productions it lists no row for -/
  sdoDefault : SdoId → Option AlgId
  /-- a nonterminal's parameters, as its rule declares them -/
  params : NtId → List ParamId
  method : SortId → MethodId → Option AlgId
  phrase : PhraseId → PhraseMeaning
  /-- whether an SDO's header declares a Completion Record -/
  sdoRc : SdoId → Bool
  /-- an SDO's number of parameters -/
  sdoArity : SdoId → Nat := fun _ => 0
  /-- each data sort's definition -/
  sortDef : SortId → Option SortDef := fun _ => none
  /-- the early-error rule rows keyed on a production -/
  early : ProdId → List EarlyRow := fun _ => []
  /-- the *SyntaxError* constructor's intrinsic -/
  syntaxError : ErrorId := 0
  /-- the specification's tables, by `TableId` -/
  table : TableId → Option Table := fun _ => none
  /-- the tables of a clause, in document order -/
  clauseTables : ClauseId → List Table := fun _ => []
  /-- the terminals of a nonterminal each of whose main-grammar right-hand sides is one terminal -/
  alts : NtId → Option (List GTerminal) := fun _ => none
  /-- the productions defined in a clause a production-in phrase names -/
  clauseProds : ClauseId → Option (List ProdId) := fun _ => none
  /-- the clause of each Annex B overlay section -/
  overlayClause : Grammar.AnnexB → Option ClauseId := fun _ => none
  /-- an SDO row by its id, for the closures it defines -/
  rowOf : AlgId → Option SdoRow := fun _ => none
  /-- the realm table: the built-in objects and the clauses' properties -/
  realm : RealmTable := {}
  /-- the erratum whose text stops at the job loop's check for a Job the clause makes -/
  jobErratum : ClauseId → Option ErratumId := fun _ => none

/-- The closures of the algorithm or SDO row that defines a closure site, and its variable count. -/
def Prog.cloOf (P : Prog) (a : AlgId) : Option (Array CloLit × Nat) :=
  match P.alg a with
  | some g => some (g.closures, g.vars.size)
  | none => (P.rowOf a).map fun r => (r.closures, r.vars.size)

/-- ClosureKind(c, kind) by c's literal: *false* for a value that is not an Abstract Closure. -/
def closureKind (P : Prog) : List (Val M) → Run M (Val M)
  | [.clo site _, .enum e] => match P.cloOf site.alg with
    | some (cs, _) => match cs[site.idx]? with
      | some c => return .bool (c.kind.enumId == some e)
      | none => Run.stop .sortError
    | none => Run.stop .sortError
  | [_, .enum _] => return .bool false
  | _ => Run.stop .sortError

def subSort (P : Prog) : Nat → SortId → SortId → Bool
  | 0, k, s => k == s
  | f + 1, k, s => k == s || (((P.sortDef k).map (·.super)).getD []).any (subSort P f · s)

/-- Membership in a sort: the `Known` sorts by the value; a Record sort by the Record's kind;
any other by its test, which is residue where the program has none. -/
def sortTest (P : Prog) (H : Host M) (call : AlgId → List (Val M) → Run M (Val M)) (s : SortId)
    (v : Val M) : Run M Bool :=
  match P.sortDef s with
  | none => v.hasSort s
  | some d =>
    let test : Run M Bool := match d.test with
      | .prim q args neg => do
        let xs := args.map (phraseArg none [v])
        let r ← bool (← if q == Known.pClosureKind then closureKind P xs
          else if hostPrim q then H.choiceL q xs else prim q xs)
        return neg != r
      | .alg a => do bool (← call a [v])
      | .none => Run.stop .residue
    match v with
    | .ref a => do
      match ← readCell a with
      | .record k _ | .env k _ _ => if d.record then return subSort P 64 k s else test
      | _ => if d.record then return false else test
    | _ => if d.record then return false else test

end Ecma
