module

public import Ecma.Ops.ProgPrim
public import Ecma.Notation.AlgKey
public import Ecma.Grammar.Derives
public import Std.Data.HashMap

@[expose] public section

/-!
# A program's source arrays, and the program they give

`Src` holds the arrays a `Prog` is built from: the algorithms, the SDO rows,
the declaration tables, the early-error rows, the tables, GL and the realm table. `Src.index` /
`Src.prog` indexes them.
-/

namespace Ecma

/-- The arrays a program is built from. -/
structure Src where
  algs : List Alg
  rows : List SdoRow
  decls : Decls
  earlyRows : List EarlyRow
  tables : List Table
  gl : Grammar.GL
  realm : RealmTable := {}

namespace Src

/-- An algorithm's name without the data's `.N` suffix for a repeated name. -/
def baseName (n : String) : String :=
  match n.splitOn "." with
  | [b, k] => if !k.isEmpty && k.all Char.isDigit then b else n
  | _ => n

def algMap (s : Src) : Std.HashMap Nat Alg := s.algs.foldl (fun m a => m.insert (algKey a.id) a) {}

/-- Each SDO row that defines closures, by its id. -/
def rowIdx (s : Src) : Std.HashMap Nat SdoRow :=
  s.rows.foldl (fun m r => if r.closures.isEmpty then m else m.insert (algKey r.id) r) {}

/-- An SDO row by its SDO and each production it is keyed by: an annex row only where no main row is. -/
def rowMap (s : Src) : Std.HashMap (SdoId × ProdId) SdoRow :=
  (SdoRow.mainLast s.rows).foldl (fun m r => r.prods.foldl (fun m p => m.insert (r.sdo, p) r) m) {}

/-- The concrete methods: a method's name, its receiver's sort, the algorithm. -/
def methodMap (s : Src) : Std.HashMap (SortId × MethodId) AlgId :=
  s.algs.foldl (fun m a => match a.header.kind, a.header.recv, s.decls.methods.idxOf? (baseName a.name) with
    | .concreteMethod, some (_, .sort _ k), some i => m.insert (k, i) a.id
    | _, _, _ => m) {}

/-- `k`'s concrete method `m` in `mm`: its own, else its first supersort's (to depth `f`); §9.1.1.3 and
§9.1.1.5 share the methods a sort does not redefine. -/
def methodOf (s : Src) (mm : Std.HashMap (SortId × MethodId) AlgId) : Nat → SortId → MethodId → Option AlgId
  | 0, _, _ => none
  | f + 1, k, m => mm[(k, m)]? <|>
    ((((s.decls.sortDefs[k]?).join).map (·.super)).getD []).findSome? (s.methodOf mm f · m)

/-- The early-error rule rows, by each production they are keyed on; where an annex rule modifies a
production's rules, its modifying rules alone. -/
def earlyMap (s : Src) : Std.HashMap ProdId (List EarlyRow) :=
  let m : Std.HashMap ProdId (List EarlyRow) := s.earlyRows.foldl (fun m r =>
    r.prods.foldl (fun m p => m.insert p ((m.getD p []) ++ [r])) m) {}
  m.map fun _ rs => if rs.any (·.modifies) then rs.filter (·.modifies) else rs

/-- The program of the arrays as they are: its maps built once, each field a lookup. -/
def index (s : Src) : Prog :=
  let algMap := s.algMap
  let rowMap := s.rowMap
  let methodMap := s.methodMap
  let earlyMap := s.earlyMap
  let rowIdx := s.rowIdx
  let tab := s.gl.tab
  { alg a := algMap[algKey a]?
    row d p := rowMap[(d, p)]?
    chain p := (tab.chainOf p).map (·.ctorIdx)
    unit p := (tab.unitOf p).map (·.ctorIdx)
    terms := tab.termsOf
    sdoDefault d := (s.decls.sdoDefaults[d]?).join
    params := tab.paramsOf
    method := s.methodOf methodMap 64
    sdoRc d := sdoRc s.decls.sdoHeaders d
    sdoArity d := sdoArity s.decls.sdoHeaders d
    sortDef k := (s.decls.sortDefs[k]?).join
    early p := earlyMap.getD p []
    syntaxError := (s.decls.fields.idxOf? "SyntaxError").getD 0
    table t := s.tables[t]?
    clauseTables c := s.tables.filter fun t => t.clause == c && !t.rows.isEmpty
    alts k := (s.decls.alts.find? (·.1 == k)).map (·.2)
    clauseProds c := (s.decls.clauseProds.find? (·.1 == c)).map (·.2)
    overlayClause a := s.decls.clauses.idxOf? a.clause
    rowOf a := rowIdx[algKey a]?
    realm := s.realm
    jobChecked c := s.decls.checkedJobs.contains c }

/-- The program. -/
def prog (s : Src) : Prog := s.index

end Src

end Ecma
