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

/-- A cell's role, from its column's header. -/
inductive CellRole where
  | head
  | name
  | type
  | sig
  | step
  | prose
  | data
  deriving Repr, BEq, Inhabited

/-- A table's type phrase: a header type, or `a List of Records with fields …`. -/
inductive TTy where
  | ty (t : TyExpr)
  /-- `a List of Records with fields [[F]] (T) and …` -/
  | records (fs : List (FieldId × TyExpr))

/-- A signature's name: `[[M]]` (a field id), or `M` (a concrete-method id). -/
inductive SigName where
  | internal (f : FieldId)
  | method (m : MethodId)
  deriving Repr, BEq, Inhabited

/-- A signature's parameter: `optional _x_: T`. -/
structure SigParam where
  x : Slot
  ty : TTy
  optional : Bool

/-- `[[M]] ( _p_: T, … ): R` or `M ( ): R`. -/
structure Sig where
  name : SigName
  params : List SigParam
  ret : TTy

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
  /-- a data cell no form fits, verbatim, with its residue channel -/
  | kept (ch : Channel) (s : String)
  /-- a header or a description, verbatim -/
  | text (s : String)

instance : Inhabited CellBody := ⟨.text ""⟩

/-- A cell: blank lines before it, `th` or `td`, attributes, layout, role, content. `block`: the
content on its own lines, two columns in; else between the tags. -/
structure TableCell where
  gap : Nat
  head : Bool
  attrs : List Attr
  block : Bool
  role : CellRole
  body : CellBody

/-- A row: blank lines before it, attributes, cells. -/
structure TableRow where
  gap : Nat
  attrs : List Attr
  cells : List TableCell

/-- An `emu-table`: its key, the column of its tag, attributes, its `emu-caption` and its `table`
element's attributes, whether it is a step's own table (a `figure`, printed with its step), kind,
rows (the first in `thead` if `thead`), the record schema it declares (from its caption, singular;
`true` if it adds to an inherited one), and its variables. -/
structure Table where
  clause : ClauseId
  idx : Nat
  col : Nat
  attrs : List Attr
  caption : Option String := none
  tableAttrs : List Attr := []
  figure : Bool := false
  kind : TableKind
  thead : Bool
  schema : Option (String × Bool)
  vars : Array String
  rows : List TableRow

/-- The entry at a retired table id (spec/formal/table-ids.txt keeps the number of a table the text no
longer has): a table with no rows, which `Src.clauseTables` counts as no clause's (every table of the
text has a row). -/
def Table.retired : Table :=
  { clause := 0, idx := 0, col := 0, attrs := [], kind := .data, thead := false, schema := none, vars := #[], rows := [] }

/-- A cell's `rowspan` or `colspan`: 1 if absent or not a numeral. -/
def TableCell.span (c : TableCell) (k : String) : Nat :=
  ((c.attrs.find? (·.key == k)).bind (·.value) |>.bind String.toNat?).getD 1

/-- One row's cells by column: `busy` holds, per column, the rows a cell from above still covers
below this one and that cell; each of `cs` (a `colspan` cell repeated) takes the next free column.
The next row's `busy`, and the row. -/
def gridRow : List (Nat × Option CellBody) → List TableCell → List (Nat × Option CellBody) × List (Option CellBody)
  | [], cs => (cs.map fun c => (c.span "rowspan" - 1, some c.body), cs.map fun c => some c.body)
  | (n + 1, x) :: bs, cs =>
    let (b, r) := gridRow bs cs
    ((n, x) :: b, x :: r)
  | (0, _) :: bs, c :: cs =>
    let (b, r) := gridRow bs cs
    ((c.span "rowspan" - 1, some c.body) :: b, some c.body :: r)
  | (0, _) :: bs, [] =>
    let (b, r) := gridRow bs []
    ((0, none) :: b, none :: r)

/-- The rows' cells by column, through `rowspan` and `colspan`: a spanned cell in each column and
row it covers. -/
def Table.grid (t : Table) : List (List (Option CellBody)) :=
  (t.rows.foldl (fun (acc : List (Nat × Option CellBody) × List (List (Option CellBody))) r =>
    let cs := r.cells.flatMap fun c => List.replicate (c.span "colspan") c
    let (b, row) := gridRow acc.1 cs
    (b, acc.2 ++ [row])) ([], [])).2

end Ecma
