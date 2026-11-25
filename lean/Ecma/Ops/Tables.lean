module

public import Ecma.Program

@[expose] public section

/-!
# The tables' primitives

A table's column by its heading and a row's cell by its column. The lookups themselves are the machine's
(`Ecma.Machine.tablePrim`), over the cells as code.
-/

namespace Ecma

variable {M : Model}

/-- A header's words: its text without markup tags (`<emu-not-ref>`). -/
def headWords (h : String) : String :=
  String.ofList (h.toList.foldl (fun (acc : List Char × Bool) ch =>
    if ch == '<' then (acc.1, true) else if ch == '>' then (acc.1, false)
    else if acc.2 then acc else (acc.1 ++ [ch], false)) ([], false)).1

/-- The column of table `t` headed `col` (a String), in its first row (`colOfHeads`). -/
def columnOf (t : Table) (col : Val M) : Option (Nat × Option Nat) :=
  (t.rows.head?.map (·.cells)).bind fun hs => colOfHeads (hs.map fun c => match c.body with
    | .text h => some (headWords h)
    | _ => none) col

/-- The cell of a row of `Table.grid` in column `i`, if the row has one. -/
def cellAt (r : List (Option CellBody)) (i : Nat) : Option CellBody := r[i]?.join

end Ecma
