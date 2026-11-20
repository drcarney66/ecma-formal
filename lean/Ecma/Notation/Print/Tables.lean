module

public import Ecma.Notation.Print
public import Ecma.Notation.Tables

/-!
# Ecma print: tables as spec.html's text

A table prints as its `emu-table` element, from `<emu-table` to `</emu-table>`: tags at
their columns, each cell's content printed by its form (an `emu-alg` from its algorithm's data).
-/

@[expose] public section

namespace Ecma.Print.Tables

open Ecma Ecma.Print

/-- A newline and `k` spaces. -/
def nl (k : Nat) : String := "\n" ++ spaces k

/-- `n` newlines. -/
def gaps (n : Nat) : String := String.ofList (List.replicate n '\n')

/-- An element's attributes: ` k="v" k2`. -/
def attrsText (as : List Attr) : String := String.join (as.map fun a => " " ++ attrText a)

def tty (c : Ctx) : TTy → String
  | .ty t => join (ty c t).1
  | .records fs => join (cat [words "a List of Records with fields", english "and" (fieldTys c fs)]).1

def sigName (c : Ctx) : SigName → String
  | .internal f => field c f
  | .method m => name c.d.methods m

def sigParam (c : Ctx) (p : SigParam) : String :=
  "\n  " ++ (if p.optional then "optional " else "") ++ "_" ++ name c.vars p.x ++ "_: " ++ tty c p.ty ++ ","

/-- `[[M]] ( ): R`, or the parameters one per line. -/
def sig (c : Ctx) (s : Sig) : String :=
  sigName c s.name ++ (if s.params.isEmpty then " ( )" else " (" ++ String.join (s.params.map (sigParam c)) ++ "\n)") ++
    ": " ++ tty c s.ret

/-- An algorithm's `emu-alg` element, its steps from column 0. -/
def algText (d : Decls) (algs : List Alg) (a : AlgId) : String :=
  match algs.find? (·.id == a) with
  | some al => "<emu-alg" ++ attrsText al.attrs ++ ">" ++ body' d al.vars al.closures 0 al.body ++ "</emu-alg>"
  | none => ""

mutual
/-- A cell's content, from column 0. -/
def body (c : Ctx) (algs : List Alg) : CellBody → String
  | .field f => field c f
  | .ty t => tty c t
  | .sig s => sig c s
  | .stmt s => let o := stmt c s; join o.1 ++ o.2
  | .alg a => algText c.d algs a
  | .expr e => join (expr c e).1
  | .op k => name c.d.ops k
  | .component f => name c.d.fields f
  | .name s => s
  | .lines bs => "<br>\n".intercalate (bodies c algs bs)
  | .dfn b => "<dfn>" ++ body c algs b ++ "</dfn>"
  | .code b => "`" ++ body c algs b ++ "`"
  | .link h b => "<a href=\"" ++ h ++ "\">" ++ body c algs b ++ "</a>"
  | .kept _ s => s
  | .text s => s

def bodies (c : Ctx) (algs : List Alg) : List CellBody → List String
  | [] => []
  | b :: r => body c algs b :: bodies c algs r
end

/-- A cell at column `k`: its content on its own lines at `k + 2`, or between the tags. -/
def cell (c : Ctx) (algs : List Alg) (k : Nat) (x : TableCell) : String :=
  let tag := if x.head then "th" else "td"
  let t := body c algs x.body
  let inner :=
    if x.block then
      (if t.isEmpty then "" else String.join ((t.splitOn "\n").map fun l => "\n" ++ (if l.isEmpty then "" else spaces (k + 2)) ++ l)) ++ nl k
    else t
  gaps x.gap ++ nl k ++ "<" ++ tag ++ attrsText x.attrs ++ ">" ++ inner ++ "</" ++ tag ++ ">"

/-- A row at column `k`. -/
def row (c : Ctx) (algs : List Alg) (k : Nat) (r : TableRow) : String :=
  gaps r.gap ++ nl k ++ "<tr" ++ attrsText r.attrs ++ ">" ++ String.join (r.cells.map (cell c algs (k + 2))) ++ nl k ++ "</tr>"

/-- The rows after a `thead`'s, at column `k`. -/
def rows (c : Ctx) (algs : List Alg) (k : Nat) (rs : List TableRow) : String := String.join (rs.map (row c algs k))

/-- A table's `emu-table` element; `algs` holds the algorithms its cells name. -/
def table (d : Decls) (algs : List Alg) (t : Table) : String :=
  let c : Ctx := { d, vars := t.vars, cl := #[], clos := #[], depth := 0 }
  let k := t.col
  let body := match t.thead, t.rows with
    | true, h :: rs => nl (k + 4) ++ "<thead>" ++ row c algs (k + 6) h ++ nl (k + 4) ++ "</thead>" ++ rows c algs (k + 4) rs
    | true, [] => nl (k + 4) ++ "<thead>" ++ nl (k + 4) ++ "</thead>"
    | false, rs => rows c algs (k + 4) rs
  let cap := match t.caption with
    | some x => nl (k + 2) ++ "<emu-caption>" ++ x ++ "</emu-caption>"
    | none => ""
  "<emu-table" ++ attrsText t.attrs ++ ">" ++ cap ++ nl (k + 2) ++ "<table" ++ attrsText t.tableAttrs ++ ">" ++ body ++ nl (k + 2) ++ "</table>" ++ nl k ++ "</emu-table>"

end Ecma.Print.Tables
