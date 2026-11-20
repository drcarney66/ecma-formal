module

public import Ecma.Machine.Config

@[expose] public section

/-!
# Table lookups

The lookups the specification makes in its tables (`tablePrim`: TableLookup, TableRowValue, TableAssociated,
TableColumnHas, SlotsListed), over the tables' cells as code (`CellCode`). A cell's value is an operand tree
that calls nothing of the program (`opVal`): a constant, a leaf operation, or a primitive.
-/

namespace Ecma.Machine
open Ecma

variable {M : Model}

mutual
/-- The value of an operand tree that calls nothing of the program; any other is a residue. -/
def opVal (X : Ctx M) : Op → Run M (Val M)
  | .const k => constV k
  | .leaf k args => do leaf (leafCtx X) k (← opVals X args)
  | .call (.prim q) args => do
    let xs ← opVals X args
    match progPrim (leafCtx X) X.P X.H q xs with
    | some r => r
    | none => if hostPrim q then X.H.choiceL q xs else X.H.allocL q xs
  | _ => Run.stop .residue

def opVals (X : Ctx M) : List Op → Run M (List (Val M))
  | [] => return []
  | o :: os => do return (← opVal X o) :: (← opVals X os)
end

mutual
/-- A cell's values, each line's of a cell of lines. -/
def cellVals (X : Ctx M) : CellCode → Run M (List (Val M))
  | .vals os => opVals X os
  | .lines cs => cellValsAll X cs
  | .wrap c => cellVals X c
  | .other => return []

def cellValsAll (X : Ctx M) : List CellCode → Run M (List (Val M))
  | [] => return []
  | c :: cs => do return (← cellVals X c) ++ (← cellValsAll X cs)
end

mutual
/-- Whether `key` is among a cell's values, its lines tried in order until one is; a cell with no values is a
residue. -/
def cellHas (X : Ctx M) (key : Val M) : CellCode → Run M Bool
  | .vals os => do return (← opVals X os).any (Val.same key)
  | .lines cs => cellHasAny X key cs
  | .wrap c => cellHas X key c
  | .other => Run.stop .residue

def cellHasAny (X : Ctx M) (key : Val M) : List CellCode → Run M Bool
  | [] => return false
  | c :: cs => do if ← cellHas X key c then return true else cellHasAny X key cs
end

/-- A cell's one value: a residue where it holds none or several. -/
def cellOne (X : Ctx M) (c : CellCode) : Run M (Val M) := do
  match ← cellVals X c with
  | [x] => return x
  | _ => Run.stop .residue

/-- A row's cell in column `i`, if the row has one. -/
def RowCode.cell (r : RowCode) (i : Nat) : Option CellCode := r.cells[i]?.join

/-- A row's cell in column `i.1`, its line `k` where `i.2 = some k`. -/
def RowCode.cellIn (r : RowCode) (i : Nat × Option Nat) : Option CellCode :=
  (r.cell i.1).bind fun c => match i.2, c with
    | some k, .lines cs => cs[k]?
    | _, c => some c

/-- The value in column `vi` of the first of `rows` whose cell in column `ki` has `key` among its values; no such
row fails its Assert, a cell with no single value is a residue. -/
def tableLookup (X : Ctx M) (vi ki : Nat × Option Nat) (key : Val M) : List RowCode → Run M (Val M)
  | [] => Run.stop .assertFailed
  | r :: rs => do
    match r.cellIn ki with
    | some c =>
      if ← cellHas X key c then
        match r.cellIn vi with
        | some v => cellOne X v
        | none => Run.stop .sortError
      else tableLookup X vi ki key rs
    | none => tableLookup X vi ki key rs

/-- Whether some row has `v` among the values of its cell in column `i`. -/
def tableColumnHas (X : Ctx M) (i : Nat × Option Nat) (v : Val M) : List RowCode → Run M Bool
  | [] => return false
  | r :: rs => do
    let here ← match r.cellIn i with
      | some c => cellHas X v c
      | none => pure false
    if here then return true else tableColumnHas X i v rs

/-- The fields of the rows' first column, in order. -/
def slotFields (X : Ctx M) : List RowCode → Run M (List (Val M))
  | [] => return []
  | r :: rs => do
    let fs ← match r.cell 0 with
      | some c => do pure ((← cellVals X c).filter fun | .field _ => true | _ => false)
      | none => pure []
    return fs ++ (← slotFields X rs)

/-- The internal slots a table lists: a new List of the fields of its first column. -/
def slotsOf (X : Ctx M) (rows : List RowCode) : Run M (Val M) := do listOf (← slotFields X rows)

/-- The primitives that look a table up. -/
def tableQ (q : PrimId) : Bool :=
  q == Known.pTableLookup || q == Known.pTableRowValue || q == Known.pTableColumnHas ||
    q == Known.pSlotsListed || q == Known.pTableAssociated

/-- A table with its rows after its header as code. -/
def Ctx.tableRows (X : Ctx M) (t : TableId) : Option (Table × List RowCode) :=
  (X.P.table t).bind fun tb => (X.prog.tstep t).map (tb, ·)

/-- TableLookup(t, valueColumn, keyColumn, key), TableRowValue(t, valueColumn, key) (keyed by the first column),
TableAssociated(t, key) (the second column, keyed by the first), TableColumnHas(t, column, v) and SlotsListed of
a table or of the clause holding one. -/
def tablePrim (X : Ctx M) (q : PrimId) : List (Val M) → Option (Run M (Val M))
  | [.table t] => if q == Known.pSlotsListed then some (match X.tableRows t with
      | some (_, rows) => slotsOf X rows
      | none => Run.stop .sortError) else none
  | [.table t, key] => if q == Known.pTableAssociated then some (match X.tableRows t with
      | some (_, rows) => do tableLookup X (1, none) (0, none) (← Prims.Strings.codeKey key) rows
      | none => Run.stop .sortError) else none
  | [.clause c] => if q == Known.pSlotsListed then some (match X.prog.clauseRows c with
      | [rows] => slotsOf X rows
      | _ => Run.stop .sortError) else none
  | [.table t, c, k, key] => if q == Known.pTableLookup then some (match X.tableRows t with
      | some (tb, rows) => match columnOf tb c, columnOf tb k with
        | some vi, some ki => tableLookup X vi ki key rows
        | _, _ => Run.stop .sortError
      | none => Run.stop .sortError) else none
  | [.table t, c, x] =>
    if q == Known.pTableRowValue then some (match X.tableRows t with
      | some (tb, rows) => match columnOf tb c with
        | some vi => tableLookup X vi (0, none) x rows
        | none => Run.stop .sortError
      | none => Run.stop .sortError)
    else if q == Known.pTableColumnHas then some (match X.tableRows t with
      | some (tb, rows) => match columnOf tb c with
        | some i => do return .bool (← tableColumnHas X i x rows)
        | none => Run.stop .sortError
      | none => Run.stop .sortError)
    else none
  | _ => none

end Ecma.Machine
