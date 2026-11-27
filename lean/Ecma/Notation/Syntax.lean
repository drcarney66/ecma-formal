module

public import Ecma.Gen.Known

@[expose] public section

/-!
# Ecma syntax: ECMA-262's algorithm notation as data

A concrete syntax tree of spec.html's algorithm notation (§5.2), with
semantic node kinds. `crates/spec-gen` emits it; `Print` prints it back byte for
byte. Surface variants (`Article`, `AltForm`, …) are kept for printing and are
ignored by the machine. Names are interned: every reference is a `Nat` into the
declaration tables (`Decls`), except prose, string literals and attributes.

The tree is untyped and first-order. Sorts are checked separately against the
parsed headers; the machine stops with a sort error on ill-sorted data.
-/

namespace Ecma

/-- An algorithm-local variable (§5.2, sec-algorithm-conventions): an index into `Alg.vars`. -/
abbrev Slot := Nat
/-- A record field, internal slot or method, or execution-context component (§6.1.7, sec-object-type;
§6.2.2, sec-list-and-record-specification-type; §9.4, sec-execution-contexts): `[[F]]`. -/
abbrev FieldId := Nat
/-- An enum constant (§5.2, sec-algorithm-conventions): `~normal~`. -/
abbrev EnumId := Nat
/-- A well-known intrinsic (§6.1.7.4, sec-well-known-intrinsic-objects), `%Array.prototype%`: interned as a field
name of a Realm's [[Intrinsics]]. -/
abbrev IntrinsicId := FieldId
/-- A syntax-directed operation (§5.2.3, sec-algorithm-conventions-syntax-directed-operations), by name. -/
abbrev SdoId := Nat
/-- A right-hand side of GL (§5.1.6, sec-grammar-notation): alphabetically assigned production ID (`Grammar.GL.ids`). -/
abbrev ProdId := Nat
/-- A nonterminal of GL (§5.1, sec-syntactic-and-lexical-grammars): `Grammar.NT`'s constructor index, sorted alphabetically. -/
abbrev NtId := Nat
/-- A grammatical parameter of GL (§5.1.6, sec-grammar-notation: `Yield`, `Await`, …): `Grammar.Param`'s constructor
index, sorted alphabetically. -/
abbrev ParamId := Nat
/-- A declared primitive (§5.2, sec-algorithm-conventions; §4.2, sec-hosts-and-implementations): notation-level
operations (𝔽, ℝ, ℤ, abs, floor, …) and host choices. -/
abbrev PrimId := Nat
/-- A sort name of the type-noun lexicon (§6, sec-ecmascript-data-types-and-values). -/
abbrev SortId := Nat
/-- A concrete-method name (§5.2.2, sec-algorithm-conventions-abstract-operations): `_envRec_.HasBinding(…)`. -/
abbrev MethodId := Nat
/-- A clause of spec.html (§5.2, sec-algorithm-conventions: its `id`), sorted alphabetically. -/
abbrev ClauseId := Nat

/-- An `emu-table` (§5.2, sec-algorithm-conventions), by its index in `Ecma.Gen.tables` flattened, sorted alphabetically. -/
abbrev TableId := Nat

/-- An algorithm (§5.2, sec-algorithm-conventions): a clause and its position among the clause's algorithms. -/
structure AlgId where
  clause : ClauseId
  idx : Nat
  deriving BEq, Inhabited

/-- The 𝔽 or ℤ subscript of a numeric literal (§5.2.6, sec-mathematical-operations). -/
inductive Sub where
  | none
  | f
  | z
  deriving BEq, Inhabited

/-- A numeral as written (§5.2.6, sec-mathematical-operations): `53`, `0x10FFFF` (digits kept for width and case),
and `0.05` as `frac 0 5 2` (whole part, fraction digits as a number, their count). -/
inductive Numeral where
  | dec (n : Nat)
  | hex (n : Nat) (digits : String)
  | frac (whole : Nat) (fraction : Nat) (places : Nat)
  deriving BEq, Inhabited

/-- The sign of a numeric literal (§5.2.6, sec-mathematical-operations). -/
inductive Sign where
  | none
  | plus
  | minus
  deriving BEq, Inhabited

/-- A magnitude (§5.2.6, sec-mathematical-operations): a numeral or ∞. -/
inductive Mag where
  | num (n : Numeral)
  | inf
  deriving BEq, Inhabited

/-- A value literal `*…*` (§5.2, sec-algorithm-conventions; §6.1, sec-ecmascript-language-types). -/
inductive ValLit where
  | undefined
  | null
  | true
  | false
  | str (s : String)
  | nan (sub : Sub)
  | num (sign : Sign) (m : Mag) (sub : Sub)
  /-- `*this*` -/
  | this
  /-- an error constructor's name: `*TypeError*` -/
  | err (e : IntrinsicId)
  /-- a BigInt in ECMAScript source notation: `` `1n` `` -/
  | bigN (n : Numeral)
  deriving BEq, Inhabited

/-- Logical conjunction or disjunction in a step condition (§5.2, sec-algorithm-conventions). -/
inductive Conj where
  | and
  | or
  deriving BEq, Inhabited

/-- Unary operator in an algorithm expression (§5.2.6, sec-mathematical-operations). -/
inductive UnOp where
  | neg
  /-- Boolean negation -/
  | not
  deriving BEq, Inhabited

/-- A spec datum without a literal form (§5.2, sec-algorithm-conventions): a sort, the alternative a template's
choice takes, or the value of an omitted optional part. -/
inductive DataLit where
  | sort (s : SortId)
  | choice (i : Nat)
  | absent
  deriving BEq, Inhabited

/-- §5.2.6 (sec-mathematical-operations) arithmetic operators; `pow` is `<sup>`. -/
inductive BinOp where
  | add
  | sub
  | mul
  | div
  | modulo
  | pow
  /-- `plus`, as the equation SDOs write `+` -/
  | plus
  /-- `times`, as the equation SDOs write `×` -/
  | times
  deriving BEq, Inhabited

/-- Relational comparison operators (§5.2.6, sec-mathematical-operations). -/
inductive RelOp where
  | lt
  | le
  | gt
  | ge
  | eq
  | ne
  deriving BEq, Inhabited

/-- The functions of §21.3 (sec-math-object) the steps name ("the sine of x", `ln(x)`): `Model.fn`'s argument. -/
inductive MathFn where
  | sin
  | cos
  | tan
  | asin
  | acos
  | atan
  | sinh
  | cosh
  | tanh
  | asinh
  | acosh
  | atanh
  | exp
  | expm1
  | ln
  | ln1p
  | log10
  | log2
  | cbrt
  deriving BEq, Inhabited

/-- What a call names (§5.2.2, sec-algorithm-conventions-abstract-operations): an operation by the clause defining it
(`idx` 0), or a primitive. -/
inductive Callee where
  | alg (a : AlgId)
  | prim (p : PrimId)
  deriving BEq, Inhabited

/-- A primitive's documentation (§5.2, sec-algorithm-conventions): its signature and one-line meaning ("" for notation primitives). -/
structure PrimDoc where
  sig : String
  meaning : String
  deriving BEq, Inhabited

/-- The kinds of Abstract Closure literal (§6.2.8, sec-abstract-closure). -/
inductive CloKind where
  | abstract
  | job
  | matcher
  | matcherContinuation
  | readModifyWrite
  deriving BEq, Inhabited

/-- The error constructors of `Throw a *TypeError* exception` (§6.1.7.4, sec-well-known-intrinsic-objects). -/
abbrev ErrorId := IntrinsicId

mutual
/-- Algorithm expressions (§5.2, sec-algorithm-conventions). -/
inductive Expr where
  | var (x : Slot)
  | val (v : ValLit)
  /-- a mathematical or extended mathematical value: `2`, `+∞`, `-∞` -/
  | math (sign : Sign) (m : Mag)
  | enum (e : EnumId)
  /-- a grammar parameter: `Yield`, `Await`, `Tagged`, … -/
  | param (p : ParamId)
  | intrinsic (i : IntrinsicId)
  /-- a field name used as a value: `[[Value]]` -/
  | fieldName (f : FieldId)
  /-- `|NT[+P, ~Q]|`: a grammar symbol and its parameters (`true`: `+`) -/
  | nt (n : NtId) (args : List (ParamId × Bool))
  /-- inline `<emu-grammar>`: its GL productions (one per presence of its optional symbols) -/
  | prod (ps : List ProdId)
  /-- `0x002E (FULL STOP)` -/
  | codeUnit (n : Nat) (digits : String) (name : Option String)
  /-- `U+002D (HYPHEN-MINUS)` -/
  | codePoint (n : Nat) (digits : String) (name : Option String)
  /-- `` `code` `` -/
  | code (s : String)
  /-- `` `super` `` where a grammar symbol is meant: the terminal symbol of that text -/
  | term (s : String)
  | call (f : Callee) (args : List Expr)
  /-- algorithm `a` on `args` at the Parse Node the steps run at -/
  | callAt (a : AlgId) (args : List Expr)
  /-- `the SDO of X [with argument(s) …]` -/
  | sdo (s : SdoId) (subject : Expr) (args : List Expr)
  /-- `the LexicalEnvironment of _ctx_` -/
  | component (c : FieldId) (subject : Expr)
  /-- `_e_.[[F]]` -/
  | field (e : Expr) (f : FieldId)
  /-- `_e_.[[M]](args)` -/
  | imethod (e : Expr) (m : FieldId) (args : List Expr)
  /-- `_e_.Name(args)` (§5.2.2) -/
  | cmethod (e : Expr) (m : MethodId) (args : List Expr)
  /-- closure application `_c_(args)` -/
  | apply (f : Expr) (args : List Expr)
  /-- `_l_[_i_]` -/
  | index (e : Expr) (i : Expr)
  /-- `? e` -/
  | q (e : Expr)
  /-- `! e` -/
  | bang (e : Expr)
  | un (o : UnOp) (e : Expr)
  | bin (o : BinOp) (a b : Expr)
  | paren (e : Expr)
  /-- `« a, b »` -/
  | list (es : List Expr)
  /-- `Record { [[F]]: e, … }`, `{ }`; `kind` is a sort name -/
  | record (kind : Option SortId) (fs : List (FieldId × Expr))
  /-- `the Completion Record with which _ctx_ was just resumed` -/
  | resumedWith (ctx : Expr)
  /-- `this Parse Node`: the node an SDO row runs at -/
  | thisNode
  /-- `the first |X|`, …, `|X|` (k): an occurrence of a nonterminal in this production -/
  | child (k : Nat) (n : NtId)
  /-- `|X|` of node `e` through its unit chain -/
  | childOf (e : Expr) (n : NtId)
  /-- `the *this* value` of a built-in function (§10.3.1): its algorithm's hidden slot 0 -/
  | thisValue
  /-- `NewTarget` of a built-in function: its algorithm's hidden slot 1 -/
  | newTarget
  | xref (c : ClauseId)
  /-- an Abstract Closure literal: its index in the algorithm's `closures` -/
  | closure (site : Nat)
  | table (t : TableId)
  /-- `the definition specified in <clause>`: the algorithm of `c` -/
  | definition (c : ClauseId)
  /-- `the value that k corresponds to in <table t>`: the step cell of the row `k` selects -/
  | tableStep (t : TableId) (key : Expr)
  /-- a variable read as a bound-variable hole: one not yet bound is `.absent` -/
  | bnd (x : Slot)
  | data (d : DataLit)
  /-- a condition's Boolean as a value -/
  | ofCond (c : Cond)

/-- A predicate of a subject (§5.2, sec-algorithm-conventions): `is v`, `is not either a String or a Symbol`, `is present`. -/
inductive Pred where
  | isVal (neg neither : Bool) (vs : List Expr)
  | isTy (neg neither : Bool) (ts : List TyExpr)
  /-- `f` on `args` and then the subject, a Boolean; negated when `neg` -/
  | call (f : Callee) (args : List Expr) (neg : Bool)

/-- Conditions of If, Assert, Repeat while/until (§5.2, sec-algorithm-conventions). -/
inductive Cond where
  /-- a subject and the predicates it shares: `e is finite and is not v` -/
  | preds (e : Expr) (p : Pred) (rest : List (Conj × Pred))
  | rel (o : RelOp) (a b : Expr)
  | and (cs : List Cond)
  | or (cs : List Cond)
  | paren (c : Cond)
  /-- `the following algorithm returns *true*:` -/
  | alg (a : AlgId)
  /-- an expression's value, a Boolean -/
  | expr (e : Expr)
  /-- an unchecked condition by its key: an Assert passes over it, elsewhere a residue -/
  | pass (key : String)

/-- Type expressions (§5.2, sec-algorithm-conventions; §6, sec-ecmascript-data-types-and-values):
header types and the type nouns of steps. -/
inductive TyExpr where
  | sort (mods : List SortId) (s : SortId)
  | listOf (t : TyExpr)
  | seqOf (t : TyExpr)
  | butNot (base exc : TyExpr)
  | doc (text : String)
  | union (ts : List TyExpr)
  /-- `a normal completion containing T` -/
  | completion (normal : Option TyExpr)
  /-- `an integer in the inclusive interval from a to b` -/
  | interval (t : TyExpr) (lo hi : Expr)
  | value (v : Expr)
  | var (x : Slot)
  | nt (n : NtId)
  | record (fs : List (FieldId × TyExpr))
  /-- `an Object that has a [[F]] internal slot` -/
  | that (t : TyExpr) (p : Pred) (rest : List (Conj × Pred))
  /-- a predicate as a type: only a pass writes it -/
  | pred (p : Pred)
end

/-- The place `Set` writes (§5.2, sec-algorithm-conventions). -/
inductive Place where
  | var (x : Slot)
  | field (e : Expr) (f : FieldId)
  | expr (e : Expr)

mutual
/-- A step's body (§5.2, sec-algorithm-conventions): an inline statement (`If c, return x.`) or nested steps. -/
inductive Body where
  | inline (s : Stmt)
  | block (ns : List Stmt)

/-- Statement forms (§5.2, sec-algorithm-conventions). -/
inductive Stmt where
  | let_ (x : Slot) (e : Expr)
  | set (p : Place) (e : Expr)
  | ret (e : Option Expr)
  | perform (e : Expr)
  /-- `If c, then` / `If c, S.`, with the `Else if` and `Else` steps that follow it -/
  | if_ (c : Cond) (b : Body) (arms : List Arm) (els : Option Arm)
  /-- `If c, S1; else S2.` -/
  | ifElse (c : Cond) (s1 s2 : Stmt)
  | assert (c : Cond)
  | assertAlways (c : Cond)
  /-- `Assert: If c, then d.` -/
  | assertIf (c d : Cond)
  /-- `Assert: This step is never reached.` and the `assert-meta` forms -/
  | unreachable (v : Nat)
  | throwVal (e : Expr)
  | note (text : String)
  | repeat_ (b : List Stmt)
  | repeatWhile (c : Cond) (b : List Stmt)
  | repeatUntil (c : Cond) (b : List Stmt)
  /-- `For each element e of L, do` / `For each T e of L, do`; `ty` for the typed form; `rev` for reverse List order -/
  | forEach (x : Slot) (ty : Option TyExpr) (l : Expr) (rev : Bool) (b : Body)
  /-- `For each Record { [[A]], [[B]] } r of L, do` -/
  | forEachRec (fs : List FieldId) (x : Slot) (l : Expr) (b : Body)
  /-- `For each integer i such that lo ≤ i < hi, in ascending order, do` -/
  | forRange (x : Slot) (lo : Expr) (loIncl : Bool) (hi : Expr) (hiIncl : Bool) (desc : Bool) (b : Body)
  /-- `For each own property key _P_ of _O_ such that _c_, in … order, do` -/
  | forKeys (x : Slot) (o : Expr) (c : Cond) (order : Nat) (b : Body)
  /-- `For each index _i_ of _L_, do` -/
  | forIndex (x : Slot) (l : Expr) (b : Body)
  /-- `For each child node _child_ of this Parse Node, do` -/
  | forChildren (x : Slot) (b : Body)
  /-- `For each child node _child_ of E, do` -/
  | forChildrenOf (x : Slot) (e : Expr) (b : Body)
  /-- `Repeat _n_ times:` -/
  | repeatN (n : Expr) (b : List Stmt)
  /-- `Suspend _ctx_.` (`v` 0); `Suspend _ctx_ and remove it from the execution context stack.` (1) -/
  | suspend (ctx : Expr) (v : Nat)
  /-- `Push _ctx_ onto the execution context stack; _ctx_ is now the running execution context.` -/
  | push (ctx : Expr) (v : Nat)
  /-- `Remove _ctx_ from the execution context stack and restore the execution context that is at
  the top of the execution context stack as the running execution context.` -/
  | remove (ctx : Expr) (v : Nat)
  /-- `Remove _ctx_ from the execution context stack and restore _r_ as the running execution context.` -/
  | removeRestore (ctx r : Expr)
  /-- `Resume the context that is now on the top of the execution context stack as the running
  execution context.` -/
  | resumeTop
  /-- `Resume the suspended evaluation of _ctx_ passing _c_ as the result of the operation that
  suspended it. Let _x_ be the Completion Record passed by the resumed computation.` -/
  | resumeLet (ctx c : Expr) (x : Slot)
  /-- `Resume _ctx_, passing _c_.` -/
  | resume (ctx c : Expr)
  /-- `Set the code evaluation state of _ctx_ such that when evaluation is resumed for that execution
  context, _clo_ will be called with no arguments.` -/
  | setCodeState (ctx clo : Expr)
  /-- a block of steps (for instance, a macro expansion) -/
  | block (ns : List Stmt)

/-- An `Else if c, …` step (`c` present) or an `Else, …` step (`c` absent) (§5.2, sec-algorithm-conventions). -/
inductive Arm where
  | mk (c : Option Cond) (b : Body)
end

instance : Inhabited Expr := ⟨.var 0⟩
instance : Inhabited Pred := ⟨.isVal false false []⟩
instance : Inhabited Cond := ⟨.and []⟩
instance : Inhabited TyExpr := ⟨.doc ""⟩
instance : Inhabited Stmt := ⟨.ret none⟩
instance : Inhabited Body := ⟨.block []⟩
instance : Inhabited Arm := ⟨.mk none (.block [])⟩

/-- An Abstract Closure literal (§6.2.8, sec-abstract-closure): `a new Abstract Closure with parameters (…)
that captures … and performs the following steps when called:`. Its slots are the algorithm's. -/
structure CloLit where
  kind : CloKind
  /-- `atomically` -/
  atomic : Bool
  /-- `none`: "with no parameters" -/
  params : Option (List Slot)
  caps : List Slot
  body : List Stmt
  /-- this, NewTarget, the passed arguments List: slots a built-in call binds -/
  frame : Option (Slot × Slot × Slot) := none

/-- An algorithm's kind (§5.2, sec-algorithm-conventions), from its clause's `type`. -/
inductive AlgKind where
  | ao
  | sdo
  | builtin
  | internalMethod
  | concreteMethod
  | numericMethod
  | hostDefined
  | implDefined
  | untyped
  deriving BEq, Inhabited

/-- A parameter (§5.2, sec-algorithm-conventions): its variable, type (structured headers only), whether it is optional
(`optional _x_`, `[ , _x_ ]`) and whether it is a rest parameter (`..._args_`). -/
structure Param where
  x : Slot
  ty : Option TyExpr
  optional : Bool
  rest : Bool

/-- A parsed structured header (§5.2, sec-algorithm-conventions: `<h1>` and `dl.header`). -/
structure Header where
  kind : AlgKind
  params : List Param
  ret : Option TyExpr
  /-- the `for:` receiver and its type -/
  recv : Option (Slot × TyExpr)

/-- One algorithm (§5.2, sec-algorithm-conventions; §5.2.2, sec-algorithm-conventions-abstract-operations):
a clause's definition with its header and variable table. -/
structure Alg where
  id : AlgId
  name : String
  header : Header
  /-- variable names by slot, without underscores: the receiver, the parameters, then the rest -/
  vars : Array String
  body : List Stmt
  /-- the Abstract Closure literals, in text order -/
  closures : Array CloLit

/-- How an SDO row is written: an `emu-alg` after its `emu-grammar`, or an equation bullet. -/
inductive RowForm where
  | alg
  | equation
  deriving BEq, Inhabited

/-- A row of a syntax-directed operation: the productions it is keyed by, and its body. -/
structure SdoRow where
  id : AlgId
  sdo : SdoId
  prods : List ProdId
  /-- the row's grammar keys as written -/
  keys : List String
  form : RowForm
  /-- variable names by slot: the SDO's parameters first -/
  vars : Array String
  body : List Stmt
  closures : Array CloLit
  /-- an annex clause's row for its SDO ("are augmented with the following", "is extended as follows") -/
  annex : Bool := false

/-- The rows with the annex rows first, so that a later main row on the same key replaces them. -/
def SdoRow.mainLast (rs : List SdoRow) : List SdoRow := rs.filter (·.annex) ++ rs.filter (!·.annex)

/-- An argument of a `SortTest` (§6, sec-ecmascript-data-types-and-values): the value itself (`subject`), or an enum constant. -/
inductive SortArg where
  | subject
  | enum (e : EnumId)
  deriving BEq, Inhabited

/-- A runtime membership test for a data sort (§6, sec-ecmascript-data-types-and-values): none, an algorithm, or a primitive on `SortArg`s. -/
inductive SortTest where
  | none
  | alg (a : AlgId)
  | prim (p : PrimId) (args : List SortArg) (neg : Bool)
  deriving BEq, Inhabited

/-- A data sort (§6, sec-ecmascript-data-types-and-values): its direct supertypes, and its test (the value is the
subject); a Record sort's values are the Records of its kind and of its subsorts'. -/
structure SortDef where
  super : List SortId := []
  test : SortTest := .none
  /-- its values are the Records of this kind -/
  record : Bool := false
  deriving BEq, Inhabited

/-- A terminal of a grammar's right-hand side (§5.1.6, sec-grammar-notation): its source text, or a code point by its
name in Tables 34 and 35 (`<USP>` the Space_Separator class). -/
inductive GTerminal where
  | text (s : String)
  | cp (name : String)
  deriving BEq, Inhabited

/-- The declaration tables (§5.1, sec-syntactic-and-lexical-grammars; §5.2, sec-algorithm-conventions):
names by id, for printing and resolution. -/
structure Decls where
  clauses : Array String
  /-- per clause, the operation it defines (its `aoid` or title), or "" -/
  ops : Array String
  fields : Array String
  enums : Array String
  sdos : Array String
  methods : Array String
  nts : Array String
  /-- GL's grammatical parameters, by `ParamId` -/
  params : Array String
  prods : Array String
  prims : Array String
  /-- per primitive, its documentation -/
  primDocs : Array PrimDoc
  sorts : Array String
  /-- each sort's definition, by `SortId`; none for `Known`'s sorts, which the value decides -/
  sortDefs : Array (Option SortDef) := #[]
  /-- each SDO's header (params and return type), by SDO -/
  sdoHeaders : Array (Option Header)
  /-- per SDO, the algorithm its clause gives every production it lists no row for, by `SdoId` -/
  sdoDefaults : Array (Option AlgId) := #[]
  /-- clauses whose Job completions are checked in every mode (§9.5) -/
  checkedJobs : Array ClauseId := #[]
  /-- the nonterminals each of whose main-grammar right-hand sides is one terminal, with those
  terminals in grammar order -/
  alts : Array (NtId × List GTerminal) := #[]
  /-- per clause a production-in phrase names, the productions defined in it -/
  clauseProds : Array (ClauseId × List ProdId) := #[]

/-! Names the machine refers to: numeric IDs come from `Ecma.Gen.Known`. -/
namespace Known

/-- `NewError`: the helper clause constructing `*Error*` objects. -/
@[reducible] def algNewError : AlgId := ⟨cNewError, 0⟩

end Known

/-- The enum of ClosureKind that names a literal's kind; none for "a new Abstract Closure". -/
def CloKind.enumId : CloKind → Option EnumId
  | .abstract => none
  | .job => some Known.eJob
  | .matcher => some Known.eMatcher
  | .matcherContinuation => some Known.eMatcherContinuation
  | .readModifyWrite => some Known.eReadModifyWrite

/-- A field written as an expression, as a place: its field and subject. -/
def Expr.fieldPlace? : Expr → Option (FieldId × Expr)
  | .component f s => some (f, s)
  | _ => none

end Ecma
