module

public import Ecma.Notation.Syntax

/-!
# Ecma tables: spec.html's `emu-table`s as data

Each table keeps its layout (attributes, `thead`, blank lines, cell layout) for printing; its
cells are typed by their column's role: field names, type phrases, method signatures, steps,
expressions and operation names, descriptions as plain strings. A table is keyed by its clause
and its index among that clause's tables.
-/

@[expose] public section

namespace Ecma

/-- A table's kind, from its header row. -/
inductive TableKind where
  /-- a Record's fields: Field Name / Value / Meaning -/
  | fields
  /-- an object's internal slots: Internal Slot / Type / Description -/
  | slots
  /-- essential internal methods: Internal Method / Description / Definitions -/
  | internalMethods
  /-- a record type's abstract methods: Method / Purpose / Definitions -/
  | abstractMethods
  /-- execution-context state components: Component / Purpose -/
  | components
  /-- an interface's properties: Property / Value / Requirements -/
  | properties
  /-- well-known intrinsics: Intrinsic Name / Global Name / ECMAScript Language Association -/
  | intrinsics
  /-- a conversion by argument type: Argument Type / Result -/
  | conversion
  /-- any other table -/
  | data
  deriving Repr, BEq, Inhabited

/-- A table's type phrase: a header type, or `a List of Records with fields …`. -/
inductive TTy where
  | ty (t : TyExpr)
  /-- `a List of Records with fields [[F]] (T) and …` -/
  | records (fs : List (FieldId × TyExpr))
  deriving Inhabited

/-- A signature's name: `[[M]]` (a field id), or `M` (a concrete-method id). -/
inductive SigName where
  | internal (f : FieldId)
  | method (m : MethodId)
  deriving BEq, Inhabited

/-- A signature's parameter: `optional _x_: T`. -/
structure SigParam where
  x : Slot
  ty : TTy
  optional : Bool
  deriving Inhabited

/-- `[[M]] ( _p_: T, … ): R` or `M ( ): R`. -/
structure Sig where
  name : SigName
  params : List SigParam
  ret : TTy
  deriving Inhabited

/-- A cell's content. -/
inductive CellBody where
  /-- `[[F]]` -/
  | field (f : FieldId)
  | ty (t : TTy)
  | sig (s : Sig)
  | stmt (s : Stmt)
  /-- an `emu-alg`, printed from that algorithm's data -/
  | alg (a : AlgId)
  | expr (e : Expr)
  /-- an operation's name, by its defining clause: `ToInt8`, `Number::add` -/
  | op (c : ClauseId)
  /-- an execution-context component's name: `Realm` -/
  | component (f : FieldId)
  /-- a global binding's name: `Int8Array` -/
  | name (s : String)
  /-- lines separated by `<br>` -/
  | lines (cs : List CellBody)
  /-- `<dfn>c</dfn>` -/
  | dfn (c : CellBody)
  /-- a code point in code: `` `U+0009` `` -/
  | code (c : CellBody)
  /-- `<a href="h">c</a>` -/
  | link (h : String) (c : CellBody)
  /-- a data cell no form fits, verbatim -/
  | raw (s : String)
  /-- a header or a description, verbatim -/
  | text (s : String)

instance : Inhabited CellBody := ⟨.text ""⟩

/-- A table cell: spans and content. -/
structure TableCell where
  rowspan : Nat := 1
  colspan : Nat := 1
  body : CellBody

/-- A table row: its cells. -/
structure TableRow where
  cells : List TableCell

/-- An `emu-table`: its key, optional caption, kind, whether row 0 is in `thead`, optional schema
(and whether it inherits), its variables, and its rows. -/
structure Table where
  clause : ClauseId
  idx : Nat
  caption : Option String := none
  kind : TableKind
  thead : Bool
  schema : Option (String × Bool)
  vars : Array String
  rows : List TableRow

/-- The entry at a retired table id (`spec/ids/table-ids.txt`): a table with no rows, which
`Src.clauseTables` excludes. -/
def Table.retired : Table :=
  { clause := 0, idx := 0, kind := .data, thead := false, schema := none, vars := #[], rows := [] }

/-- One row's cells by column: `busy` holds, per column, the rows a cell from above still covers
below this one and that cell; each of `cs` (a `colspan` cell repeated) takes the next free column.
The next row's `busy`, and the row. -/
def gridRow : List (Nat × Option CellBody) → List TableCell → List (Nat × Option CellBody) × List (Option CellBody)
  | [], cs => (cs.map fun c => (c.rowspan - 1, some c.body), cs.map fun c => some c.body)
  | (n + 1, x) :: bs, cs =>
    let (b, r) := gridRow bs cs
    ((n, x) :: b, x :: r)
  | (0, _) :: bs, c :: cs =>
    let (b, r) := gridRow bs cs
    ((c.rowspan - 1, some c.body) :: b, some c.body :: r)
  | (0, _) :: bs, [] =>
    let (b, r) := gridRow bs []
    ((0, none) :: b, none :: r)

/-- The rows' cells by column, through `rowspan` and `colspan`: a spanned cell in each column and
row it covers. -/
def Table.grid (t : Table) : List (List (Option CellBody)) :=
  (t.rows.foldl (fun (acc : List (Nat × Option CellBody) × List (List (Option CellBody))) r =>
    let cs := r.cells.flatMap fun c => List.replicate c.colspan c
    let (b, row) := gridRow acc.1 cs
    (b, acc.2 ++ [row])) ([], [])).2

end Ecma
