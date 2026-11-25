module

public import Ecma.Prims.Lists
public import Ecma.Prims.Strings
public import Ecma.Prims.CharSets
public import Ecma.Prims.Records
public import Ecma.Prims.Context
public import Ecma.Prims.Nodes
public import Ecma.Prims.Numbers
public import Ecma.Notation.Early
public import Ecma.Notation.Tables

@[expose] public section

/-!
# Parsing

A parser invocation (`newParse`), a cover's reparse (§5.1.5, `reparse`), ParseText's goal (`parseGoal`), JSON
text, and which Annex B sections the host supports.
-/

namespace Ecma

variable {M : Model}

/-- §5.1.5: a cover's parameters, the values the covering node was parsed with. -/
def coverArgs (ps : List ParamId) (n : M.Node) : List (ParamId × Bool) :=
  ps.map fun p => (p, (M.nodeArgs n).any (·.ctorIdx == p))

/-- A new parser invocation under `cx`: its stamp, recorded as strict from outside, for ParseJSON, of
eval code processed by a direct eval (`direct`), or within a |Module|. -/
def newParse (cx : ParseCx) (direct : Bool := false) : Run M Nat := fun s =>
  let strictParses := if cx.strict then s.parses :: s.strictParses else s.strictParses
  let jsonParses := if cx.json then s.parses :: s.jsonParses else s.jsonParses
  let directParses := if direct then s.parses :: s.directParses else s.directParses
  let moduleParses := if cx.module then s.parses :: s.moduleParses else s.moduleParses
  .ok s.parses { s with parses := s.parses + 1, strictParses, jsonParses, directParses, moduleParses }

/-- A parse's outcome, its root Parse Node recorded. -/
def withRoot (r : Option (Option M.Node)) : Run M (Option (Option M.Node)) := fun s =>
  match r with
  | some (some n) => .ok r { s with roots := s.roots.insert (M.nodeStamp n) n }
  | _ => .ok r s

/-- The context of the invocation that made `n`, with the Annex B sections `annexB`. -/
def parseCxOf (annexB : Grammar.AnnexB.Set) (n : M.Node) : Run M ParseCx := do
  let s ← Run.get
  return ⟨annexB, s.strictParses.contains (M.nodeStamp n), s.jsonParses.contains (M.nodeStamp n),
    s.moduleParses.contains (M.nodeStamp n)⟩

/-- B.3.3: `n`'s source with `{` before and `}` after each child |FunctionDeclaration|, each then the sole
StatementListItem of a BlockStatement. -/
def asIfSource (n : M.Node) : M.Seq M.Math :=
  let fs := Prims.Nodes.asIfSpans n
  (seqList (M.nodeSource n)).zipIdx.foldl (fun s (c, i) =>
    let s := if fs.any (·.1 == i) then M.seqPush s (M.ofNat 123) else s
    let s := M.seqPush s c
    if fs.any (·.2 == i + 1) then M.seqPush s (M.ofNat 125) else s) M.seqNil

/-- §5.1.2: the parse of `n`'s source with goal `k`, a new parser invocation
in the context of the one that made `n`; once per `n` and `k` that gives a node, the covered node being
unique for a given cover: the node the model gives from the cover itself (`Model.cover`), else the parse
of the cover's source text. With `k` `n`'s own nonterminal, B.3.3's processing as an |IfStatement|: the
parse of the source `asIfSource n`. -/
def reparse (annexB : Grammar.AnnexB.Set) (ps : List ParamId) (n : M.Node) (k : NtId) :
    Run M (Option (Option M.Node)) := do
  match (← Run.get).covered.find? (fun (c, k', _) => k' == k && Val.same (.node c) (.node n)) with
  | some (_, _, r) => return some (some r)
  | none =>
    let cx ← parseCxOf annexB n
    let st ← newParse cx ((← Run.get).directParses.contains (M.nodeStamp n))
    (fun s => .ok () { s with covers := (st, n) :: s.covers } : Run M Unit)
    let r ← withRoot (match (if k == M.nodeNt n then none else M.cover cx st n k (coverArgs ps n)) with
      | some c => some (some c)
      | none => M.parse cx st (if k == M.nodeNt n then asIfSource n else M.nodeSource n) k (coverArgs ps n))
    if let some (some c) := r then
      (fun s => .ok () { s with covered := (n, k, c) :: s.covered } : Run M Unit)
    return r

/-- §5.1.2 ParseGoal(text, goal), and ParseGoal(text, goal, strict, json[, direct]):
a new parser invocation over a List of code points, strict from outside, for ParseJSON and of eval code
processed by a direct eval as given, within a |Module| when the goal is |Module|. -/
def parseGoal (annexB : Grammar.AnnexB.Set) (vs : List (Val M)) : Run M (Val M) :=
  match (match vs with
    | [l, g] => [l, g, .bool false, .bool false, .bool false]
    | [l, g, s, j] => [l, g, s, j, .bool false]
    | _ => vs) with
  | [.ref a, .nt k ps, .bool strict, .bool json, .bool direct] => do
    match ← readCell a with
    | .list xs _ =>
      match M.seqFoldl (fun acc v => match acc, v with
          | some s, .math c => some (M.seqPush s c)
          | _, _ => none) (some M.seqNil) xs with
      | some cps => do
        let cx : ParseCx := ⟨annexB, strict, json, k == Grammar.NT.Module.ctorIdx⟩
        let st ← newParse cx direct
        match ← withRoot (M.parse cx st cps k ps) with
        | some (some n) => return .node n
        | some none => return .enum Known.eEmpty
        | none => Run.stop .residue
      | none => Run.stop .sortError
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- IsJSONText(cps): whether the List of code points cps derives from the JSON grammar's |JSONText|, a new
parser invocation in no context. -/
def isJSONText (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [l] => do
    let xs ← Prims.Strings.seqOf l
    match M.seqFoldl (fun acc v => match acc, v with
        | some s, .math c => if Prims.Strings.isPoint c then some (M.seqPush s c) else none
        | _, _ => none) (some M.seqNil) xs with
    | some cps => do
      let cx : ParseCx := ⟨{}, false, false, false⟩
      let st ← newParse cx
      match M.parse cx st cps Grammar.NT.JSONText.ctorIdx [] with
      | some r => return .bool r.isSome
      | none => Run.stop .residue
    | none => Run.stop .sortError
  | _ => Run.stop .sortError

end Ecma
