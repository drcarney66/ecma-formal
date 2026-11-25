module

public import Engine.Accel.Algs
public import Std.Data.HashSet

@[expose] public section

/-!
# The debugger's names and values as shown

`Names` is what an engine's adapter names for the debugger: algorithms (sec-id, name), step paths,
fields, enums, sorts, nonterminals and productions. The core never reads `Ecma.Gen`; the machine's
adapter (`Debugger.Machine`) fills these from it.

`val` prints every form of `Val` one level deep (docs/debugger/state.md §3, §5): a String as a
JS string literal (lone surrogates escaped), a Number as JS prints it, a mathematical value exactly,
an enum as `~name~`, an object or a Record or List by identity (`#addr`, expandable by its
`variablesReference`, addr + 1), a Completion Record with its fields, a closure by its algorithm and
captures, an algorithm by name, a Parse Node by production and span.
-/

namespace Debugger

open Ecma Engine.Model

abbrev F := Engine.Impl

/-- A listed step: its path and text as a frame's (within `reading`), SpecTec text, depth and sub-steps. -/
structure ListingStep where
  path : String
  text : String
  spectec : String := ""
  depth : Nat
  reading : Option String := none
  steps : List ListingStep := []

/-- An algorithm or SDO row as listed: name, sec-id, index, kind, productions, parameters, SpecTec header, steps. -/
structure Listing where
  name : String
  secId : String
  idx : Nat
  kind : String
  production : Option String := none
  params : List String := []
  spectecHead : String := ""
  steps : List ListingStep

/-- What the adapter names: algorithms' sec-ids and names, the algorithms a breakpoint's `alg`
names, step paths as written, and the notation's tables (fields, enums, sorts, nonterminals,
productions, SDOs, clauses), the statement rows and nonterminals (`stmtNtNames`), and each
algorithm's or SDO row's listing. -/
structure Names where
  secId : AlgId → String := fun _ => "?"
  name : AlgId → String := fun _ => "?"
  resolve : String → List AlgId := fun _ => []
  pathText : List Nat → String := fun _ => ""
  parsePath : String → Option (List Nat) := fun _ => none
  field : FieldId → String := fun f => s!"field{f}"
  /-- a field by its name (`Strict`), for the views that read one -/
  fieldId : String → Option FieldId := fun _ => none
  enum : EnumId → String := fun e => s!"enum{e}"
  sort : SortId → String := fun s => s!"sort{s}"
  nt : NtId → String := fun n => s!"nt{n}"
  /-- a production as written: `ExpressionStatement : Expression ;` -/
  prod : ProdId → String := fun p => s!"prod{p}"
  clause : ClauseId → String := fun c => s!"clause{c}"
  /-- the SDO rows (clause, index) a statement node's evaluation can enter first -/
  stmtRows : Std.HashSet (Nat × Nat) := {}
  /-- the statement nonterminals -/
  stmtNts : Std.HashSet NtId := {}
  /-- an algorithm's or SDO row's steps, printed as its frames' steps are -/
  algorithm : AlgId → Option Listing := fun _ => none

/-- The nonterminals whose nodes are statements for statement stepping. -/
def stmtNtNames : List String :=
  ["ExpressionStatement", "VariableStatement", "LexicalDeclaration", "ClassDeclaration", "IfStatement",
    "BreakableStatement", "IterationStatement", "DoWhileStatement", "WhileStatement", "ForStatement", "ForInOfStatement",
    "ContinueStatement", "BreakStatement", "ReturnStatement", "WithStatement", "SwitchStatement", "ThrowStatement",
    "DebuggerStatement", "ExpressionBody"]

/-- The SDOs that evaluate a statement node. -/
def stmtSdoNames : List String :=
  ["Evaluation", "LabelledEvaluation", "LoopEvaluation", "DoWhileLoopEvaluation", "WhileLoopEvaluation",
    "ForLoopEvaluation", "ForInOfLoopEvaluation"]

/-- A variable's name: an alias as written, a call's temporary (`#` then words) as its words, an
unnamed slot as `t<n>`. -/
def slotName (vars : Array String) (i : Nat) : String :=
  match vars[i]? with
  | some n => if n.startsWith "#" then (n.drop 1).toString else if n.isEmpty then s!"t{i}" else n
  | none => s!"t{i}"

/-! Step paths as written. -/

def romanValue (c : Char) : Nat :=
  match c with
  | 'i' => 1 | 'v' => 5 | 'x' => 10 | 'l' => 50 | 'c' => 100 | 'd' => 500 | 'm' => 1000 | _ => 0

/-- Lower-case Roman numerals' value (subtractive), 0 for none. -/
def romanOf (s : String) : Nat :=
  let vs := s.toList.map romanValue
  let n : Int := (vs.zip (vs.drop 1 ++ [0])).foldl (fun n (v, w) => if v < w then n - v else n + v) 0
  if vs.contains 0 then 0 else n.toNat

/-- Lower-case letters' value (a = 1, z = 26, aa = 27), 0 for none. -/
def alphaOf (s : String) : Nat :=
  if s.all fun c => 'a' ≤ c && c ≤ 'z' then s.foldl (fun n c => n * 26 + (c.toNat - 'a'.toNat + 1)) 0 else 0

/-- One level of a step path: its number, if `s` is written as `levelText d` writes it. -/
def levelOf (levelText : Nat → Nat → String) (d : Nat) (s : String) : Option Nat :=
  let n := match d % 3 with
    | 0 => s.toNat?.getD 0
    | 1 => alphaOf s
    | _ => romanOf s
  if n > 0 && levelText d n == s then some n else none

/-- A step path as written (`2.a.ii`, a trailing `.` allowed), innermost first, its levels as
`levelText` writes them. -/
def parsePathBy (levelText : Nat → Nat → String) (s : String) : Option (List Nat) :=
  let s := if s.endsWith "." then (s.dropEnd 1).toString else s
  if s.isEmpty then none
  else ((s.splitOn ".").zipIdx.mapM fun (t, d) => levelOf levelText d t).map List.reverse

namespace Show

/-! Strings and numbers. -/

def hex4 (n : Nat) : String :=
  let h := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (4 - h.length) '0') ++ h

/-- One code unit outside a surrogate pair, escaped as in a JS string literal. -/
def unit (u : Nat) : String :=
  if 0xD800 ≤ u && u < 0xE000 then "\\u" ++ hex4 u
  else match Char.ofNat u with
    | '"' => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | '\x08' => "\\b"
    | '\x0c' => "\\f"
    | '\x0b' => "\\v"
    | c => if u < 0x20 || u == 0x7F || u == 0x2028 || u == 0x2029 then "\\u" ++ hex4 u else String.singleton c

def units : List Nat → String
  | [] => ""
  | u :: l :: r =>
    if 0xD800 ≤ u && u < 0xDC00 && 0xDC00 ≤ l && l < 0xE000 then
      String.singleton (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00))) ++ units r
    else unit u ++ units (l :: r)
  | [u] => unit u

/-- A String value as a JS string literal: a surrogate pair as its code point, a lone surrogate
and a control escaped. -/
def str (s : Array UInt16) : String := "\"" ++ units (s.toList.map (·.toNat)) ++ "\""

/-- Code units as text: a pair as its code point, a lone surrogate as U+FFFD. -/
def text (s : Array UInt16) : String :=
  String.ofList (go (s.toList.map (·.toNat)))
where
  go : List Nat → List Char
    | [] => []
    | u :: l :: r =>
      if 0xD800 ≤ u && u < 0xDC00 && 0xDC00 ≤ l && l < 0xE000 then
        Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)) :: go r
      else one u :: go (l :: r)
    | [u] => [one u]
  one (u : Nat) : Char := if 0xD800 ≤ u && u < 0xE000 then '�' else Char.ofNat u

/-- A double's bits, in hex. -/
def bits (x : F.Num) : String :=
  let b : BitVec 64 := Engine.Model.Num.bits x
  "0x" ++ String.ofList (Nat.toDigits 16 b.toNat)

/-- A Number as JS prints it (Number::toString), -0 as `-0`; its bits where that declines. -/
def num (x : F.Num) : String :=
  match F.numView x with
  | .negZero => "-0"
  | _ => (Engine.Accel.numberToString 10 x).getD s!"(double {bits x})"

/-- `n / d` exactly: a decimal where `d` has no prime factor but 2 and 5, else the fraction. -/
def ratText (q : Rat) : String :=
  if q.den == 1 then toString q.num
  else
    let rec strip (fuel d k2 k5 : Nat) : Nat × Nat × Nat := match fuel with
      | 0 => (d, k2, k5)
      | f + 1 =>
        if d % 2 == 0 then strip f (d / 2) (k2 + 1) k5
        else if d % 5 == 0 then strip f (d / 5) k2 (k5 + 1)
        else (d, k2, k5)
    let (rest, k2, k5) := strip 128 q.den 0 0
    if rest != 1 then s!"{q.num}/{q.den}"
    else
      let k := max k2 k5
      -- |q| · 10^k is an integer
      let n := q.num.natAbs * 2 ^ (k - k2) * 5 ^ (k - k5)
      let ds := toString n
      let ds := String.ofList (List.replicate (k + 1 - min (k + 1) ds.length) '0') ++ ds
      let whole := (ds.dropEnd k).toString
      let frac := (ds.takeEnd k).toString
      (if q.num < 0 then "-" else "") ++ whole ++ "." ++ frac

/-- A mathematical value, exactly. -/
def math : MathVal → String
  | .int i => toString i
  | .frac q _ => ratText q

/-! Parse Nodes. -/

/-- A production as written, from its nonterminal on: `ExpressionStatement : Expression ;`. -/
def prodText (n : Names) (nt : NtId) (p : ProdId) : String :=
  let full := n.prod p
  match full.splitOn (n.nt nt ++ " :") with
  | _ :: rest@(_ :: _) => n.nt nt ++ " :" ++ (n.nt nt ++ " :").intercalate rest
  | _ => full

/-- A Parse Node by production and span: `ExpressionStatement : Expression ; [3, 9)`. -/
def node (n : Names) : F.Node → String
  | .mk _ lo hi p nt _ _ _ => s!"{prodText n nt p} [{lo}, {hi})"

/-! Values. -/

/-- An address as a number. -/
def addr (a : F.Addr) : Nat := a

def bigText (b : F.Big) : String := let i : Int := b; toString i

/-- A cell's `variablesReference`: its address + 1, 0 for a value that has none. -/
def ref : Val F → Nat
  | .obj a | .ref a => addr a + 1
  | _ => 0

/-- A value's sort, as a `type`. -/
def type : Val F → String
  | .absent => "absent"
  | .missing => "missing"
  | .undefined => "Undefined"
  | .null => "Null"
  | .bool _ => "Boolean"
  | .str _ => "String"
  | .sym _ => "Symbol"
  | .num _ => "Number"
  | .big _ => "BigInt"
  | .obj _ => "Object"
  | .math _ | .posInf | .negInf => "mathematical value"
  | .enum _ => "enum"
  | .ref _ => "Record or List"
  | .comp .. => "Completion Record"
  | .clo .. => "Abstract Closure"
  | .alg _ => "algorithm"
  | .node _ => "Parse Node"
  | .leaf .. => "Parse Node (terminal)"
  | .term _ => "terminal"
  | .ty .. => "type"
  | .cond .. => "condition"
  | .field _ => "field"
  | .nt .. => "nonterminal"
  | .param _ => "grammar parameter"
  | .prod _ => "production"
  | .sort _ => "sort"
  | .choice _ => "choice"
  | .clause _ => "clause"
  | .table _ => "table"
  | .unbound => "unbound"
  | .tuple _ => "tuple"

/-- A value, its parts (`deep`) shown one level further. -/
def valAt (n : Names) (deep : Bool) : Val F → String
  | .absent => "absent"
  | .missing => "missing"
  | .undefined => "undefined"
  | .null => "null"
  | .bool b => toString b
  | .str s => str s
  | .sym (i, some d) => s!"Symbol({str d}) #{i}"
  | .sym (i, none) => s!"Symbol() #{i}"
  | .num x => num x
  | .big b => s!"{bigText b}n"
  | .obj a | .ref a => s!"#{addr a}"
  | .math m => math m
  | .posInf => "+∞"
  | .negInf => "-∞"
  | .enum e => s!"~{n.enum e}~"
  | .comp t v g =>
    if deep then s!"Completion \{ type: ~{n.enum t}~, value: {valAt n false v}, target: {valAt n false g} }"
    else s!"Completion(~{n.enum t}~)"
  | .clo site caps =>
    let head := s!"closure {n.name site.alg}#{site.idx}"
    if !deep || caps.isEmpty then head
    else head ++ " capturing [" ++ ", ".intercalate (caps.map (valAt n false)) ++ "]"
  | .alg a => n.name a
  | .node nd => node n nd
  | .leaf nd i t => s!"the terminal `{t}` (item {i}) of {node n nd}"
  | .term t => s!"`{t}`"
  | .ty .. => "a type"
  | .cond .. => "a condition"
  | .field f => s!"[[{n.field f}]]"
  | .nt nt args => n.nt nt ++ (if args.isEmpty then "" else
      "[" ++ ", ".intercalate (args.map fun (p, b) => (if b then "+" else "~") ++ toString p) ++ "]")
  | .param p => s!"param {p}"
  | .prod ps => " | ".intercalate (ps.map n.prod)
  | .sort s => n.sort s
  | .choice i => s!"choice {i}"
  | .clause c => n.clause c
  | .table t => s!"table {t}"
  | .unbound => "unbound"
  | .tuple vs => s!"({vs.length} values)"

/-- A value as shown: one level deep. -/
def val (n : Names) (v : Val F) : String := valAt n true v

end Show

end Debugger
