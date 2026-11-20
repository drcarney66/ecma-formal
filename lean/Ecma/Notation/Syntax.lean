module

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

/-- An algorithm-local variable: an index into `Alg.vars`. -/
abbrev Slot := Nat
/-- A record field, internal slot or method, or execution-context component: `[[F]]`. -/
abbrev FieldId := Nat
/-- An enum constant: `~normal~`. -/
abbrev EnumId := Nat
/-- A well-known intrinsic, `%Array.prototype%`: interned as a field name of a Realm's [[Intrinsics]]. -/
abbrev IntrinsicId := FieldId
/-- A syntax-directed operation, by name. -/
abbrev SdoId := Nat
/-- A right-hand side of GL: the number spec/formal/prod-ids.txt gives it (`Grammar.GL.ids`). -/
abbrev ProdId := Nat
/-- A nonterminal of GL: `Grammar.NT`'s constructor index, the number spec/formal/nt-ids.txt gives it. -/
abbrev NtId := Nat
/-- A grammatical parameter of GL (`Yield`, `Await`, …): `Grammar.Param`'s constructor index, the number
spec/formal/param-ids.txt gives it. -/
abbrev ParamId := Nat
/-- A domain phrase class: a row of the phrase table. -/
abbrev PhraseId := Nat
/-- A declared primitive: notation-level operations (𝔽, ℝ, ℤ, abs, floor, …) and channel (b). -/
abbrev PrimId := Nat
/-- A sort name of the type-noun lexicon. -/
abbrev SortId := Nat
/-- A concrete-method name (§5.2.2): `_envRec_.HasBinding(…)`. -/
abbrev MethodId := Nat
/-- A clause of spec.html (its `id`), in document order. -/
abbrev ClauseId := Nat

/-- An `emu-table`, by its index in `Ecma.Gen.tables` flattened: the number spec/formal/table-ids.txt gives it. -/
abbrev TableId := Nat

/-- An algorithm: a clause and its position among the clause's algorithms. -/
structure AlgId where
  clause : ClauseId
  idx : Nat
  deriving BEq, Inhabited

/-- A step or element attribute, as written: `[id="step-foo"]`, `normative-optional`. -/
structure Attr where
  key : String
  value : Option String
  deriving BEq, Inhabited

/-- `<emu-xref>`'s form. -/
inductive XrefForm where
  | plain
  | title
  | content (text : String)
  deriving BEq, Inhabited

structure Xref where
  href : String
  form : XrefForm
  /-- the clause the href names, if it names one (tables and other targets do not) -/
  clause : Option ClauseId
  deriving BEq, Inhabited

/-- The 𝔽 or ℤ subscript of a literal. -/
inductive Sub where
  | none
  | f
  | z
  deriving BEq, Inhabited

/-- A numeral as written: `53`, `0x10FFFF` (digits kept for width and case), and `0.05`
as `frac 0 5 2` (whole part, fraction digits as a number, their count). -/
inductive Numeral where
  | dec (n : Nat)
  | hex (n : Nat) (digits : String)
  | frac (whole : Nat) (fraction : Nat) (places : Nat)
  deriving BEq, Inhabited

inductive Sign where
  | none
  | plus
  | minus
  deriving BEq, Inhabited

/-- A magnitude: a numeral or ∞. -/
inductive Mag where
  | num (n : Numeral)
  | inf
  deriving BEq, Inhabited

/-- A value literal `*…*` (§5.2: ECMAScript language values and Number/BigInt values). -/
inductive ValLit where
  | undefined
  | null
  | true
  | false
  /-- `s` decoded; `w` as written where it is not `s` re-escaped (`&`, `<`), else "" -/
  | str (s : String) (w : String)
  | nan (sub : Sub)
  | num (sign : Sign) (m : Mag) (sub : Sub)
  /-- `*this*` -/
  | this
  /-- an error constructor's name: `*TypeError*` -/
  | err (e : IntrinsicId)
  /-- a BigInt in ECMAScript source notation: `` `1n` `` -/
  | bigN (n : Numeral)
  deriving BEq, Inhabited

/-- `the X of Y` against `X of Y`. -/
inductive Article where
  | the
  | none
  deriving BEq, Inhabited

/-- `is either A or B`, `is one of A, B`, `is A or B`, `is neither A nor B`. -/
inductive AltForm where
  | either
  | oneOf
  | or
  | neither
  deriving BEq, Inhabited

/-- A connective's surface: `A and B`, `A, and B`, `A, B, and C`; `A, or if B`. -/
inductive ConnForm where
  | plain
  | comma
  | orIf
  /-- `both of the following conditions are true: c1 and c2` (`all` for more; `any` for or) -/
  | following
  deriving BEq, Inhabited

inductive Conj where
  | and
  | or
  deriving BEq, Inhabited

/-- How a list of expressions is written. -/
inductive ListForm where
  /-- `(a, b)` -/
  | paren
  /-- `a, b` -/
  | comma
  /-- `a and b`, `a, b, and c` (or `or`) -/
  | english (c : Conj)
  /-- continuation lines `* a` after the step -/
  | bullets
  deriving BEq, Inhabited

inductive UnOp where
  | neg
  /-- Boolean negation -/
  | not
  deriving BEq, Inhabited

/-- A spec datum without a literal form: a sort, the alternative a template's choice takes, or the value
of an omitted optional part. -/
inductive DataLit where
  | sort (s : SortId)
  | choice (i : Nat)
  | absent
  deriving BEq, Inhabited

/-- §5.2.6's arithmetic; `pow` is `<sup>`. -/
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

inductive RelOp where
  | lt
  | le
  | gt
  | ge
  | eq
  | ne
  deriving BEq, Inhabited

/-- The functions of §21.3 the steps name ("the sine of x", `ln(x)`): `Model.fn`'s argument. -/
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

/-- What a call names: an operation by the clause defining it (`idx` 0), or a primitive. -/
inductive Callee where
  | alg (a : AlgId)
  | prim (p : PrimId)
  deriving BEq, Inhabited

/-- Where a residual prose node goes (the three visible channels). -/
inductive Channel where
  /-- not yet assigned: a visible stop in the machine -/
  | pending
  /-- (a) a spec-issue candidate (`Decls.reasons`), meaning `p` meanwhile if declared -/
  | upstream (reason : Nat) (p : Option PrimId)
  /-- (b) a declared primitive: applied to the prose's holes in order when `wired` (they are
  its signature's arguments), else a visible stop -/
  | prim (p : PrimId) (wired : Bool)
  /-- (c) annotated prose of a kind (`Decls.notes`: prose Assert, choice, host-defined), meaning `p` if declared -/
  | annotated (kind : Nat) (p : Option PrimId)
  deriving BEq, Inhabited

/-- A live prose channel's primitive (prose calls it on the holes); none for a residue channel. -/
def Channel.live? : Channel → Option PrimId
  | .prim q true | .upstream _ (some q) | .annotated _ (some q) => some q
  | _ => none

/-- A primitive's documentation: its signature and one-line meaning, as the overlay or the
residue classifier states them ("" for the notation primitives the machine defines). -/
structure PrimDoc where
  sig : String
  meaning : String
  deriving BEq, Inhabited

/-- An erratum, by its row of the overlay's readings table. -/
abbrev ErratumId := Nat

/-- A reading of an erratum's step: the pinned text, what test262 requires, or our fix. -/
inductive Reading where
  | literal
  | test262
  | proposed
  /-- the overlay's reading of prose steps (`<emu-reading steps=…>`), the only one it gives -/
  | definition
  deriving BEq, Inhabited

/-- The alternative a step's readings take under the errata's readings `rd`: a definition reading's (its one
alternative, `.definition`) whatever `rd` says, for it is no choice; an erratum's, the one `rd e` names if the step
has it (else the pinned step, `none`). -/
def Reading.pick {α : Type} (rd : ErratumId → Reading) (e : ErratumId) : List (Reading × α) → Option (Reading × α)
  | [(.definition, a)] => some (.definition, a)
  | alts => alts.find? (·.1 == rd e)

/-- The kinds of Abstract Closure literal. -/
inductive CloKind where
  | abstract
  | job
  | matcher
  | matcherContinuation
  | readModifyWrite
  deriving BEq, Inhabited

/-- The error constructors of `Throw a *TypeError* exception`. -/
abbrev ErrorId := IntrinsicId

mutual
/-- Expressions. -/
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
  | prod (ps : List ProdId) (raw : String)
  /-- `0x002E (FULL STOP)` -/
  | codeUnit (n : Nat) (digits : String) (name : Option String)
  /-- `U+002D (HYPHEN-MINUS)` -/
  | codePoint (n : Nat) (digits : String) (name : Option String)
  /-- `` `code` ``: decoded; `w` as written where it is not `s` re-escaped, else "" -/
  | code (s : String) (w : String)
  /-- `` `super` `` where a grammar symbol is meant: the terminal symbol of that text -/
  | term (s : String)
  | call (f : Callee) (args : List Expr)
  /-- algorithm `a` on `args` at the Parse Node the steps run at -/
  | callAt (a : AlgId) (args : List Expr)
  /-- `the SDO of X [with argument(s) …]`; `ctxRead` for execution-context components -/
  | sdo (s : SdoId) (a : Article) (subject : Expr) (args : List Expr)
  /-- `the LexicalEnvironment of _ctx_` -/
  | component (c : FieldId) (a : Article) (subject : Expr)
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
  /-- `! e` at a site of erratum `r` (readings.emu `stops=`): an abrupt completion stops as `r` -/
  | bangAt (r : ErratumId) (e : Expr)
  /-- `e` at a site of erratum `r`: a failed check in it, its callees' included, stops as `r` (a caller's
  step), and when `sort` a sort error too (a field chain) -/
  | erratum (r : ErratumId) (sort : Bool) (e : Expr)
  | un (o : UnOp) (e : Expr)
  | bin (o : BinOp) (a b : Expr)
  | paren (e : Expr)
  /-- `« a, b »` -/
  | list (es : List Expr)
  /-- `Record { [[F]]: e, … }`, `the Completion Record { … }`, `{ }`; `kind` is a sort name -/
  | record (a : Article) (kind : Option SortId) (fs : List (FieldId × Expr))
  /-- `the Completion Record with which _ctx_ was just resumed` -/
  | resumedWith (ctx : Expr)
  /-- `this Parse Node`: the node an SDO row runs at -/
  | thisNode
  /-- `the first |X|`, `the second |X|`, `the third |X|` (k 0–2), `the fourth |X|` (7), `the derived |X|` (3), `the |X|` (4),
  `|X|` (5): an occurrence of a nonterminal in this production's right-hand side; `|X|` (6): its
  left-hand side, the Parse Node itself; elsewhere `|X|` is a grammar symbol (`nt`) -/
  | child (k : Nat) (n : NtId) (suffix : String)
  /-- `|X|` inside `If |Y| is <emu-grammar>P</emu-grammar>` with `X` on P's right-hand side: the child
  of the node `e` (`|Y|`) -/
  | childOf (e : Expr) (n : NtId) (suffix : String)
  /-- `the *this* value` (`bare`: `*this* value`) of a built-in function (§10.3.1): its algorithm's
  hidden slot 0 -/
  | thisValue (bare : Bool)
  /-- `NewTarget` of a built-in function: its algorithm's hidden slot 1 -/
  | newTarget
  /-- `<emu-meta effects="…">e</emu-meta>` -/
  | annot (attrs : List Attr) (e : Expr)
  | xref (x : Xref)
  /-- an Abstract Closure literal: its index in the algorithm's `closures` -/
  | closure (site : Nat)
  /-- an `emu-xref` to table `t` -/
  | table (t : TableId) (x : Xref)
  /-- `the definition specified in <xref>`: the algorithm of the clause `x` names; `asSpecified` when written `Set p as specified in <xref>` -/
  | definition (x : Xref) (asSpecified : Bool)
  /-- `the value that k corresponds to in <table t>`: the step cell of the row `k` selects -/
  | tableStep (t : TableId) (key : Expr) (x : Xref)
  /-- `the largest T _x_ (closest to +∞) such that c` (`max`), or `the smallest … (closest to -∞) …` -/
  | extreme (max : Bool) (x : Slot) (ty : TyExpr) (c : Cond)
  | phrase (p : PhraseId) (holes : List Hole)
  | prose (ch : Channel) (parts : List Part)
  /-- a variable read as a bound-variable hole: one not yet bound is `.absent` -/
  | bnd (x : Slot)
  | data (d : DataLit)
  /-- a condition's Boolean as a value -/
  | ofCond (c : Cond)

/-- A predicate of a subject: `is v`, `is not either a String or a Symbol`, `is present`. -/
inductive Pred where
  | isVal (neg : Bool) (f : AltForm) (vs : List Expr)
  | isTy (neg : Bool) (f : AltForm) (ts : List TyExpr)
  | phrase (p : PhraseId) (holes : List Hole)
  /-- `f` on `args` and then the subject, a Boolean; negated when `neg` -/
  | call (f : Callee) (args : List Expr) (neg : Bool)

/-- Conditions of If, Assert, Repeat while/until. -/
inductive Cond where
  /-- a subject and the predicates it shares: `e is finite and is not v` -/
  | preds (e : Expr) (p : Pred) (rest : List (Conj × Pred))
  | rel (o : RelOp) (a b : Expr)
  | and (f : ConnForm) (cs : List Cond)
  | or (f : ConnForm) (cs : List Cond)
  | paren (c : Cond)
  /-- `the following algorithm returns *true*:` and algorithm `a`'s `emu-alg` (printed as its
  own), run at the rule's Parse Node -/
  | alg (a : AlgId)
  /-- a condition phrase: `the host is a web browser`, `lo ≤ x < hi` -/
  | phrase (p : PhraseId) (holes : List Hole)
  | prose (ch : Channel) (parts : List Part)
  /-- an expression's value, a Boolean -/
  | expr (e : Expr)
  /-- an unchecked condition by its key: an Assert passes over it, elsewhere a residue -/
  | pass (key : String)

/-- Type expressions: header types and the type nouns of steps. -/
inductive TyExpr where
  /-- `a Number`, `an ordinary object`, `the Property Descriptor`; modifiers are sort names;
  `w`: the sort's words as written where they are another form of its name (a plural), else "" -/
  | sort (a : String) (mods : List SortId) (s : SortId) (w : String)
  | listOf (a : String) (t : TyExpr)
  /-- `A or B`, `either A, B, or C`, `one of …`; `comma` for `either A, or B` (a nested list before) -/
  | union (f : AltForm) (c : ConnForm) (ts : List TyExpr)
  /-- `a normal completion containing T` -/
  | completion (normal : Option TyExpr)
  /-- `an integer in the inclusive interval from a to b` -/
  | interval (t : TyExpr) (lo hi : Expr)
  | value (v : Expr)
  /-- `a _t_`: the type a type hole holds; the article as written -/
  | var (a : String) (x : Slot)
  /-- `a |X|`; the article as written, possibly empty -/
  | nt (a : String) (n : NtId) (suffix : String)
  | record (fs : List (FieldId × TyExpr))
  /-- `an Object that has a [[F]] internal slot` -/
  | that (t : TyExpr) (p : Pred) (rest : List (Conj × Pred))
  | phrase (p : PhraseId) (holes : List Hole)
  | prose (parts : List Part)
  /-- a predicate as a type: only a pass writes it -/
  | pred (p : Pred)

/-- An argument of a phrase: its kind is fixed by the phrase table's template. -/
inductive Hole where
  | e (x : Expr)
  | c (x : Cond)
  | t (x : TyExpr)
  /-- a variable the phrase binds -/
  | b (x : Slot)
  /-- a condition over the variables `xs` the phrase binds, in their order: a test of its candidates -/
  | bc (xs : List Slot) (x : Cond)
  /-- the alternative a template's choice takes, by index (an optional: 0 present, 1 absent) -/
  | w (i : Nat)
  | l (f : ListForm) (xs : List Expr)
  /-- words as written: a table column's name; after a step's template, its continuation
  lines, indented from the step's marker -/
  | text (s : String)
  /-- words naming a field or component, as its name is written: `the Generator component of e` -/
  | field (f : FieldId)

/-- A piece of residual prose: verbatim text, or a typed hole inside it. -/
inductive Part where
  | text (s : String)
  | hole (h : Hole)
end

/-- The place `Set` writes. -/
inductive Place where
  | var (x : Slot)
  | field (e : Expr) (f : FieldId)
  | expr (e : Expr)

mutual
/-- A step's body: an inline statement (`If c, return x.`) or nested steps. -/
inductive Body where
  | inline (s : Stmt)
  | block (ss : List Node)

/-- Statement forms (§5.2 and the spec's conventions). Repeated forms that differ only in
surface keep a variant index `v`, printed by the form's table and ignored by the machine. -/
inductive Stmt where
  | let_ (x : Slot) (e : Expr)
  /-- `Let x be e, and let y be f.`-style forms with several binders -/
  | letMany (xs : List Slot) (e : Expr) (v : Nat)
  | set (p : Place) (e : Expr)
  | ret (e : Option Expr)
  | perform (e : Expr)
  /-- `If c, then` / `If c, S.`, with the `Else if` and `Else` steps that follow it -/
  | if_ (c : Cond) (b : Body) (arms : List Arm) (els : Option Arm)
  /-- `If c, S1; else S2.` -/
  | ifElse (c : Cond) (s1 s2 : Stmt)
  | assert (c : Cond)
  /-- `Assert: c` at a site of erratum `r`, checked in every mode: a false `c` stops as `r`; `none` at a
  site with a caller condition, a failed Assert that the caller's `erratum` relabels -/
  | assertAt (r : Option ErratumId) (c : Cond)
  /-- `Assert: If c, then d.` -/
  | assertIf (c d : Cond)
  /-- `Assert: This step is never reached.` and the `assert-meta` forms -/
  | unreachable (v : Nat)
  /-- `Throw a *TypeError* exception.` -/
  | throwErr (e : ErrorId)
  | throwVal (e : Expr)
  | note (text : List Part)
  | repeat_ (b : List Node)
  | repeatWhile (c : Cond) (b : List Node)
  | repeatUntil (c : Cond) (b : List Node)
  /-- `For each element e of L, do` / `For each T e of L, do`; `ty` for the typed form; `rev` for reverse List order -/
  | forEach (x : Slot) (ty : Option TyExpr) (l : Expr) (rev : Bool) (b : Body)
  /-- `For each Record { [[A]], [[B]] } r of L, do` -/
  | forEachRec (fs : List FieldId) (x : Slot) (l : Expr) (b : Body)
  /-- `For each integer i such that lo ≤ i < hi, in ascending order, do` -/
  | forRange (x : Slot) (lo : Expr) (loIncl : Bool) (hi : Expr) (hiIncl : Bool) (desc : Bool) (b : Body)
  /-- `Append e to L.`, `Remove …`, `Insert …`, … : the spec's mutations, by phrase -/
  | mutate (p : PhraseId) (holes : List Hole)
  /-- `For each _T_ _x_ such that _c_, do` over a domain the text names only by _T_ and _c_ -/
  | forSuchThat (x : Slot) (ty : TyExpr) (c : Cond) (order : Option Nat) (b : Body)
  /-- `For each own property key _P_ of _O_ such that _c_, in … order, do`; order 0 ascending numeric
  index, 1 ascending chronological order of property creation, 2 descending numeric index -/
  | forKeys (x : Slot) (o : Expr) (c : Cond) (order : Nat) (b : Body)
  /-- `For each index _i_ of _L_, do` -/
  | forIndex (x : Slot) (l : Expr) (b : Body)
  /-- `For each child node _child_ of this Parse Node, do` -/
  | forChildren (x : Slot) (b : Body)
  /-- `For each child node _child_ of E, do` -/
  | forChildrenOf (x : Slot) (e : Expr) (b : Body)
  /-- `Repeat _n_ times:` -/
  | repeatN (n : Expr) (b : List Node)
  /-- `Return _e_ (see xref).`: `Return _e_` -/
  | retSee (e : Expr) (see : Xref)
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
  | resumeLet (ctx c : Expr) (x : Slot) (annot : List Attr)
  /-- `Resume _ctx_, passing _c_.` -/
  | resume (ctx c : Expr)
  /-- `Set the code evaluation state of _ctx_ such that when evaluation is resumed for that execution
  context, _clo_ will be called with no arguments.` -/
  | setCodeState (ctx clo : Expr)
  /-- a step with an erratum: the pinned step, and the other readings' steps (`<emu-reading>`) -/
  | readings (e : ErratumId) (lit : Stmt) (alts : List (Reading × List Node))
  /-- `Find a T _x_ such that c; but if this is not possible (reason), S.` -/
  | findSuchThat (x : Slot) (ty : TyExpr) (c : Cond) (reason : String) (fail : Stmt)
  /-- `Let _xs_ be integers such that c, and o is as small as possible`: the slots bound to integers
  c holds of, best on `objs` in order (`true`: as large as possible, `false`: as small as possible) -/
  | letSuchThat (xs : List Slot) (c : Cond) (objs : List (Bool × Expr))
  /-- `IfAbruptRejectPromise(e, cap).` and the other shorthand macros -/
  | macro (m : AlgId) (args : List Expr)
  | phrase (p : PhraseId) (holes : List Hole)
  | prose (ch : Channel) (parts : List Part)
  /-- a phrase, mutation or prose step and its nested steps, which its form does not take -/
  | withSteps (s : Stmt) (sub : List Node)
  /-- a macro use with its expansion's steps, their parameters renamed to the use's variables
  (`Alg.expandMacros`) -/
  | expanded (m : AlgId) (args : List Expr) (body : List Node)

/-- A numbered step: its attributes and statement; layout is regenerated from depth. -/
inductive Node where
  | mk (attrs : List Attr) (s : Stmt)

/-- An `Else if c, …` step (`c` present) or an `Else, …` step (`c` absent), with its attributes. -/
inductive Arm where
  | mk (attrs : List Attr) (c : Option Cond) (b : Body)
end

instance : Inhabited Expr := ⟨.var 0⟩
instance : Inhabited Pred := ⟨.isVal false .or []⟩
instance : Inhabited Cond := ⟨.and .plain []⟩
instance : Inhabited TyExpr := ⟨.prose []⟩
instance : Inhabited Stmt := ⟨.ret none⟩
instance : Inhabited Node := ⟨.mk [] default⟩

/-- An Abstract Closure literal: `a new Abstract Closure with parameters (…) that captures …
and performs the following steps when called:`. Its slots are the algorithm's. -/
structure CloLit where
  kind : CloKind
  /-- `atomically` -/
  atomic : Bool
  /-- `none`: "with no parameters" -/
  params : Option (List Slot)
  caps : List Slot
  body : List Node
  /-- this, NewTarget, the passed arguments List: slots a built-in call binds -/
  frame : Option (Slot × Slot × Slot) := none

/-- An algorithm's kind, from its clause's `type`. -/
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

/-- A parameter: its variable, type (structured headers only), whether it is optional
(`optional _x_`, `[ , _x_ ]`) and whether it is a rest parameter (`..._args_`). -/
structure Param where
  x : Slot
  ty : Option TyExpr
  optional : Bool
  rest : Bool

/-- A parsed structured header (`<h1>` and `dl.header`). -/
structure Header where
  kind : AlgKind
  params : List Param
  ret : Option TyExpr
  /-- the `for:` receiver and its type -/
  recv : Option (Slot × TyExpr)
  /-- `description:` prose -/
  desc : List Part

/-- One algorithm: a clause's `emu-alg` with its header and variable table. -/
structure Alg where
  id : AlgId
  name : String
  header : Header
  /-- variable names by slot, without underscores: the receiver, the parameters, then the rest -/
  vars : Array String
  /-- the `emu-alg` element's own attributes -/
  attrs : List Attr
  /-- the column of the `emu-alg` tag; steps sit two columns in, two more a level -/
  indent : Nat
  body : List Node
  /-- the Abstract Closure literals, in text order -/
  closures : Array CloLit

/-- How an SDO row is written: an `emu-alg` after its `emu-grammar`, or an equation bullet. -/
inductive RowForm where
  | alg (attrs : List Attr)
  | equation
  deriving BEq, Inhabited

/-- A row of a syntax-directed operation: the productions it is keyed by, and its body.
Children are referred to as `|NT|` (`Expr.nt`) and resolved against the row's productions. -/
structure SdoRow where
  id : AlgId
  sdo : SdoId
  prods : List ProdId
  /-- the row's grammar keys as written, one per `<emu-grammar>` (the productions' text, which
  `ecma-print` prints and `scripts/bijection.py` compares with spec.html's) -/
  keys : List String
  form : RowForm
  /-- the column of the `emu-alg` tag -/
  indent : Nat
  /-- variable names by slot: the SDO's parameters first -/
  vars : Array String
  body : List Node
  closures : Array CloLit
  /-- an annex clause's row for its SDO ("are augmented with the following", "is extended as follows") -/
  annex : Bool := false

/-- The rows with the annex rows first, so that a later main row on the same key replaces them. -/
def SdoRow.mainLast (rs : List SdoRow) : List SdoRow := rs.filter (·.annex) ++ rs.filter (!·.annex)

/-- A constructor's `Repr` from its name and arguments, as `deriving Repr` writes it. -/
def reprCtor (f : Std.Format) (prec : Nat) : Std.Format :=
  Repr.addAppParen (.group (.nest (if prec >= max_prec then 1 else 2) f)) prec

/-- A list's `Repr` from its elements' formats, as `List.repr` writes it. -/
def reprList : List Std.Format → Std.Format
  | [] => "[]"
  | fs => Std.Format.bracket "[" (Std.Format.joinSep fs ("," ++ Std.Format.line)) "]"

/-- A template piece of the phrase table. -/
inductive Piece where
  | word (s : String)
  /-- a hole: 0 expression, 1 condition, 2 type, 3 binder, 4 steps, 5 list, 6 words -/
  | hole (kind : Nat)
  /-- alternatives (an optional part is `[part, []]`), selected by a `Hole.w` -/
  | choice (alts : List (List Piece))
  /-- no space before the next piece -/
  | glue
  deriving Inhabited

mutual
/-- `Piece`'s `Repr`, as `deriving Repr` writes it, by structural recursion (a derived one is
`partial`: `Piece` is nested). -/
def Piece.repr : Piece → Nat → Std.Format
  | .word a, prec => reprCtor ("Ecma.Piece.word" ++ .line ++ reprArg a) prec
  | .hole a, prec => reprCtor ("Ecma.Piece.hole" ++ .line ++ reprArg a) prec
  | .choice a, prec => reprCtor ("Ecma.Piece.choice" ++ .line ++ reprList (Piece.reprsAlts a)) prec
  | .glue, prec => reprCtor "Ecma.Piece.glue" prec

/-- The formats of a list of alternatives. -/
def Piece.reprsAlts : List (List Piece) → List Std.Format
  | [] => []
  | ps :: alts => reprList (Piece.reprs ps) :: Piece.reprsAlts alts

/-- The formats of a list of pieces. -/
def Piece.reprs : List Piece → List Std.Format
  | [] => []
  | p :: ps => Piece.repr p 0 :: Piece.reprs ps
end

instance : Repr Piece := ⟨Piece.repr⟩

mutual
/-- `Piece`'s `BEq`, as `deriving BEq` writes it, by structural recursion. -/
def Piece.beq : Piece → Piece → Bool
  | .word a, .word b => a == b
  | .hole a, .hole b => a == b
  | .choice a, .choice b => Piece.beqAlts a b
  | .glue, .glue => true
  | _, _ => false

/-- Two lists of alternatives are equal. -/
def Piece.beqAlts : List (List Piece) → List (List Piece) → Bool
  | [], [] => true
  | a :: as, b :: bs => Piece.beqList a b && Piece.beqAlts as bs
  | _, _ => false

/-- Two lists of pieces are equal. -/
def Piece.beqList : List Piece → List Piece → Bool
  | [], [] => true
  | a :: as, b :: bs => Piece.beq a b && Piece.beqList as bs
  | _, _ => false
end

instance : BEq Piece := ⟨Piece.beq⟩

/-- An argument of a phrase's meaning: one of its holes, an enum value, a predicate
phrase's subject, this Parse Node, or a sort. -/
inductive PhraseArg where
  | hole (i : Nat)
  /-- the last hole, a list hole: its elements, as the last arguments -/
  | spread (i : Nat)
  | enum (e : EnumId)
  | subject
  /-- the Parse Node the SDO row runs at -/
  | thisNode
  /-- a sort, as a type hole of that sort is -/
  | sort (s : SortId)
  /-- a field or internal slot name -/
  | field (f : FieldId)
  /-- an alternative of the primitive's choice, fixed -/
  | choice (k : Nat)
  deriving BEq, Inhabited

/-- What a phrase means: an algorithm of the overlay (`<emu-phrase>`), or a primitive applied
to arguments (`neg`: its negation, for a negative predicate phrase). -/
inductive PhraseMeaning where
  | alg (a : AlgId)
  | prim (p : PrimId) (args : List PhraseArg) (neg : Bool)
  | none
  deriving BEq, Inhabited

/-- Whether a phrase meaning spreads its list hole. -/
def PhraseMeaning.spreads : PhraseMeaning → Bool
  | .prim _ args _ => args.any fun | .spread _ => true | _ => false
  | _ => false

/-- A data sort: its direct supertypes, and its test (the value is the subject); a Record
sort's values are the Records of its kind and of its subsorts'. -/
structure SortDef where
  super : List SortId := []
  test : PhraseMeaning := .none
  /-- its values are the Records of this kind -/
  record : Bool := false
  /-- the predicate phrase over the context's variable that refines its test where that variable is in scope -/
  context : Option PhraseId := none
  deriving BEq, Inhabited

/-- A phrase-table row: its category (statement, expression, condition, type, place),
template, and meaning. -/
structure Phrase where
  cat : Nat
  template : List Piece
  meaning : PhraseMeaning
  deriving BEq, Inhabited

/-- A terminal of a grammar's right-hand side (§5.1.6): its source text, or a code point by its
name in Tables 34 and 35 (`<USP>` the Space_Separator class). -/
inductive GTerminal where
  | text (s : String)
  | cp (name : String)
  deriving BEq, Inhabited

/-- The declaration tables: names by id, for printing and resolution. -/
structure Decls where
  clauses : Array String
  /-- per clause, the operation it defines (its `aoid` or title), or "" -/
  ops : Array String
  fields : Array String
  enums : Array String
  sdos : Array String
  nts : Array String
  /-- GL's grammatical parameters, by `ParamId` -/
  params : Array String
  prods : Array String
  prims : Array String
  sorts : Array String
  methods : Array String
  phrases : Array Phrase
  /-- each SDO's header (params and return type), by SDO -/
  sdoHeaders : Array (Option Header)
  /-- per primitive, its documentation -/
  primDocs : Array PrimDoc
  /-- residue channel (a)'s spec-issue reasons -/
  reasons : Array String
  /-- residue channel (c)'s kinds -/
  notes : Array String
  /-- the errata, by name, in the overlay's order (spec/formal/readings.emu) -/
  errata : Array String
  /-- per erratum, the reading today's model applies (`pending` as `proposed`) -/
  parity : Array Reading
  /-- each sort's definition (`spec/formal/sorts.emu`), by `SortId`; none for `Known`'s
  sorts, which the value decides -/
  sortDefs : Array (Option SortDef) := #[]
  /-- per SDO, the algorithm its clause gives every production it lists no row for ("implicitly
  has the following default definition"), by `SdoId` -/
  sdoDefaults : Array (Option AlgId) := #[]
  /-- the nonterminals each of whose main-grammar right-hand sides is one terminal, with those
  terminals in grammar order -/
  alts : Array (NtId × List GTerminal) := #[]
  /-- per clause a production-in phrase names, the productions defined in it (with the Annex B
  overlays of a grammar it wholly defines) -/
  clauseProds : Array (ClauseId × List ProdId) := #[]
  /-- the literal errata whose text stops at the job loop's check (§9.5) for a Job its clause makes -/
  jobErrata : Array (ClauseId × ErratumId) := #[]

/-! Names the machine refers to: `crates/spec-gen` interns these first, at these indices. -/
namespace Known
def eNormal : EnumId := 0
def eThrow : EnumId := 1
def eReturn : EnumId := 2
def eEmpty : EnumId := 5
def eUnused : EnumId := 6
def eAccessor : EnumId := 7
def eData : EnumId := 8
def eDone : EnumId := 29
def eMatcher : EnumId := 121
def eMatcherContinuation : EnumId := 122
def eJob : EnumId := 123
def eReadModifyWrite : EnumId := 124
def eYield : EnumId := 126
def eOwnPropertyKeys : EnumId := 127
def eGetOwnProperty : EnumId := 128
def eGetPrototypeOf : EnumId := 129

def fType : FieldId := 0
def fValue : FieldId := 1
def fTarget : FieldId := 2
def fRealm : FieldId := 3
/-- [[Call]] -/
def fCall : FieldId := 45
def fIntrinsics : FieldId := 4
def fCodeState : FieldId := 5
def fWritable : FieldId := 6
def fGetter : FieldId := 7
def fSetter : FieldId := 8
def fEnumerable : FieldId := 9
def fConfigurable : FieldId := 10
def fFunction : FieldId := 11
def fScriptOrModule : FieldId := 12
def fLexicalEnvironment : FieldId := 13
def fVariableEnvironment : FieldId := 14
def fPrivateEnvironment : FieldId := 15
def fGenerator : FieldId := 16
def fDescription : FieldId := 17
def fPrototype : FieldId := 53
def fExtensible : FieldId := 54
def fInitialName : FieldId := 125
def fAsync : FieldId := 126
def fBehaviour : FieldId := 368
def fMostRecentLeaveEvent : FieldId := 278
def fWaiters : FieldId := 280
def fWeakRefTarget : FieldId := 111
def fCells : FieldId := 112
def fDateValue : FieldId := 211
def fKey : FieldId := 64
def fKind : FieldId := 65
def fObject : FieldId := 136
def fResult : FieldId := 281
def fAction : FieldId := 413
def fTypedArrayName : FieldId := 138
def fExports : FieldId := 144
def fProxyHandler : FieldId := 148
def fIndex : FieldId := 249
def fNames : FieldId := 100
def fName : FieldId := 66
def fGet : FieldId := 24
def fSet : FieldId := 26
def fLength : FieldId := 552
def fPrefix : FieldId := 551
def fSlots : FieldId := 553
def fConstructor : FieldId := 554
def fExotic : FieldId := 555
def fSlotValues : FieldId := 556
def fLengthAttributes : FieldId := 557
def fNameAttributes : FieldId := 558
def fProperties : FieldId := 559
def fIntrinsic : FieldId := 560
def fGlobalThis : FieldId := 561
def fOmittable : FieldId := 562
def fOptional : FieldId := 563
def fClause : FieldId := 564
def fCreated : FieldId := 565
/-- [[ParkedStack]]: an Agent Record's execution context stack while another agent runs. -/
def fParkedStack : FieldId := 566
def fCandidateExecution : FieldId := 28
def fEventsRecords : FieldId := 29
def fAgentSignifier : FieldId := 30
def fBlock : FieldId := 33
def fByteIndex : FieldId := 34
def fElementSize : FieldId := 35
def fEventList : FieldId := 37
def fSignifier : FieldId := 108

def sorts : Array String := #["Completion Record", "Number", "String", "Boolean", "Symbol", "BigInt",
  "Object", "List", "Record", "integer", "mathematical value", "extended mathematical value",
  "Parse Node", "Abstract Closure", "ECMAScript language value", "property key",
  "normal completion", "abrupt completion", "throw completion", "return completion",
  "undefined", "null", "non-negative integer", "Property Descriptor"]
def sComp : SortId := 0
def sNumber : SortId := 1
def sString : SortId := 2
def sBoolean : SortId := 3
def sSymbol : SortId := 4
def sBigInt : SortId := 5
def sObject : SortId := 6
def sList : SortId := 7
def sRecord : SortId := 8
def sInteger : SortId := 9
def sMath : SortId := 10
def sXMath : SortId := 11
def sNode : SortId := 12
def sClosure : SortId := 13
def sLangValue : SortId := 14
def sPropKey : SortId := 15
def sNormalComp : SortId := 16
def sAbruptComp : SortId := 17
def sThrowComp : SortId := 18
def sReturnComp : SortId := 19
def sUndefined : SortId := 20
def sNull : SortId := 21
def sNonNegInt : SortId := 22
/-- a Record sort outside `sorts`, at its id in spec/formal/sort-ids.txt -/
def sWaiterList : SortId := 153
def sCharSet : SortId := 132

def pF : PrimId := 0
def pR : PrimId := 1
def pZ : PrimId := 2
def pAbs : PrimId := 3
def pFloor : PrimId := 4
def pMin : PrimId := 5
def pMax : PrimId := 6
def pTruncate : PrimId := 7
def pAppend : PrimId := 8
def pPrepend : PrimId := 9
def pLength : PrimId := 11
def pEmptyString : PrimId := 13
def pConcat : PrimId := 14
def pClamp : PrimId := 15
def pOwnLookup : PrimId := 16
def pOwnCreate : PrimId := 17
def pOwnReplace : PrimId := 18
def pOwnSetAttribute : PrimId := 19
def pOwnRemove : PrimId := 20
def pHasNoFields : PrimId := 21
def pIsOrdinaryMethod : PrimId := 22
/-- The host's choice points: the first and last of them. -/
def pApprox : PrimId := 23
def pHostChoice : PrimId := 24
def pWebBrowser : PrimId := 27
/-- The notation primitives (§5.2, §6): the table of `Ecma.Ecma.Prims`. -/
def pListNew : PrimId := 28
def pListConcat : PrimId := 29
def pListLen : PrimId := 30
def pContains : PrimId := 31
def pListElem : PrimId := 32
def pListOf1 : PrimId := 33
def pCopy : PrimId := 34
def pIsEmpty : PrimId := 35
def pSameLength : PrimId := 36
def pListFind : PrimId := 37
def pCount : PrimId := 38
def pInsert : PrimId := 39
def pRemoveElem : PrimId := 40
def pRemoveFirst : PrimId := 41
def pRemoveLast : PrimId := 42
def pReverse : PrimId := 43
def pReplaceElem : PrimId := 44
def pSetAdd : PrimId := 45
def pStoreBytes : PrimId := 46
def pCodeUnit : PrimId := 47
def pStrOfUnits : PrimId := 48
def pSubstring : PrimId := 49
def pStrLen : PrimId := 50
def pUnitAt : PrimId := 51
def pNumericValue : PrimId := 52
def pFirstUnit : PrimId := 53
def pStartsWith : PrimId := 54
def pCodePointCount : PrimId := 55
def pUnitOrPointOf : PrimId := 56
def pCodePointMatched : PrimId := 57
def pCodePoints : PrimId := 58
def pEmptyCodePoints : PrimId := 59
def pSourceText : PrimId := 60
def pComponent : PrimId := 61
def pHasField : PrimId := 62
def pHasSlot : PrimId := 63
def pHasMethod : PrimId := 64
def pHasSlots : PrimId := 65
def pAttrValue : PrimId := 66
def pSlotsListed : PrimId := 67
def pNewRecord : PrimId := 68
def pPresent : PrimId := 69
/-- `the |X| of node`: the child of a Parse Node that is an instance of |X| (§5.2.2) -/
def pChildOf : PrimId := 70
def pRunning : PrimId := 71
def pCurrentRealm : PrimId := 72
def pActiveFunction : PrimId := 73
def pAgentRecord : PrimId := 74
def pSurroundingAgent : PrimId := 75
def pStackEmpty : PrimId := 76
def pIsSuspended : PrimId := 77
def pChild : PrimId := 78
def pThisNode : PrimId := 79
def pCoveredBy : PrimId := 80
def pGrammarSymbol : PrimId := 82
def pInstanceOf : PrimId := 83
/-- InParseJSONScript(n): whether `n` was made by a parser invocation for ParseJSON. -/
def pInParseJSONScript : PrimId := 136
def pIsNonterminal : PrimId := 106
def pIsGrammarSymbol : PrimId := 107
def pTableLookup : PrimId := 119
/-- MakeObject(names): a new object with an internal slot for each name, each *undefined*, and no own properties. -/
def pMakeObject : PrimId := 121
/-- BuiltinFunctionSlots(): the slots of an ordinary object and of §10.3's built-in function objects. -/
def pBuiltinFunctionSlots : PrimId := 133
def pTableColumnHas : PrimId := 167
/-- TableRowValue(t, valueColumn, key): TableLookup keyed by the table's first column. -/
def pTableRowValue : PrimId := 209
/-- TableAssociated(t, key): the second-column entry of the row of t whose first-column entry is key. -/
def pTableAssociated : PrimId := 250
def pNewBindingsRecord : PrimId := 210
/-- BindingsHas(env, N): whether `env` has a binding for the name `N`. -/
def pBindingsHas : PrimId := 223
def pBindingFor : PrimId := 212
def pAddBinding : PrimId := 213
def pRemoveBinding : PrimId := 214
def pBindingNames : PrimId := 215
/-- StrictFromOutside(n): whether `n` was made by a parser invocation of strict mode code from outside. -/
def pStrictFromOutside : PrimId := 216
/-- HasParam(n, p): whether the grammar parameter `p` was set when `n` was parsed. -/
def pHasParam : PrimId := 219
/-- GoalSymbolOf(n): the goal symbol of the parser invocation that made `n`. -/
def pGoalSymbolOf : PrimId := 220
/-- TerminalAlternatives(nt): the Strings of the terminals that are nt's right-hand sides. -/
def pTerminalAlternatives : PrimId := 246
/-- InDirectEval(n): whether `n` was made by a parser invocation of eval code processed by a direct eval. -/
def pInDirectEval : PrimId := 221
/-- StrictModeCode(n): whether the source text `n` matched is strict mode code (§11.2.2). -/
def pStrictModeCode : PrimId := 286
/-- HasUseStrictDirective(body): whether the Directive Prologue of `body` contains a Use Strict Directive. -/
def pHasUseStrictDirective : PrimId := 285
def pNearestEnclosing : PrimId := 138
def pParent : PrimId := 194
def pChildNodes : PrimId := 195
/-- IsJSONText(cps): whether the List of code points cps is a valid JSON text (ECMA-404). -/
def pIsJSONText : PrimId := 193
def pIsFinite : PrimId := 84
def pInInterval : PrimId := 85
def pParity : PrimId := 86
def pRemainder : PrimId := 87
def pXMath : PrimId := 88
def pNegative : PrimId := 89
def pNumberFor : PrimId := 90
def pBigIntFor : PrimId := 91
def pBitwise : PrimId := 92
def pPi : PrimId := 93
def pTimeConst : PrimId := 94
def pChain : PrimId := 95
def pCharSetUnion : PrimId := 96
def pCharSetOne : PrimId := 97
def pCharSetUnionAll : PrimId := 98
def pEmptyCharSet : PrimId := 296
def pCharSetInterval : PrimId := 297
def pCharSetMinus : PrimId := 298
def pCharSetAllSingle : PrimId := 299
def pCharSetSingles : PrimId := 300
def pCharSetNoScf : PrimId := 301
def pCharSetCanonExtra : PrimId := 302
def pCharSetHasCanonical : PrimId := 303
def pIsCharSet : PrimId := 304
def pChar : PrimId := 99
def pCharValue : PrimId := 100
/-- PropertyCharSet(p, v): the CharSetElements whose Unicode Character Database definition
includes the property p with the value v. -/
def pPropertyCharSet : PrimId := 174
/-- IsPropertyValueAlias(p, v): whether PropertyValueAliases.txt lists v for the property p. -/
def pIsPropertyValueAlias : PrimId := 175
/-- CanonicalPropertyValue(p, v): the long name of the value v names for the property p. -/
def pCanonicalPropertyValue : PrimId := 257
/-- RightHandSideCharacters(ss): the characters whose code points are on the right-hand sides of
the productions of the nonterminals ss. -/
def pRightHandSideCharacters : PrimId := 169
/-- An object's own property keys, as a List in the stated order (0: ascending numeric index for
array indices; 1: ascending chronological order of property creation). -/
def pKeysOrdered : PrimId := 101
/-- OwnPropertyHas(O, P): whether O has an own property whose key is P. -/
def pOwnHas : PrimId := 102
/-- OneIndexedList(n, v): a List of n copies of v, indexed 1 through n. -/
def pOneIndexedList : PrimId := 103
/-- NewDataBlock(n): a new Data Block of n bytes, each 0. -/
def pNewDataBlock : PrimId := 287
/-- StringRepeat(s, n): the String made from n copies of s appended together. -/
def pStringRepeat : PrimId := 289
/-- IntToRadix(n, radix): the representation of non-negative integer n using radix (2 to 36). -/
def pIntToRadix : PrimId := 305
/-- ParseNodesWithin(n): n and the Parse Nodes of nonterminals it contains, a node before its children. -/
def pParseNodesWithin : PrimId := 290
/-- ListFindOf(t, f, l, v): the element of l of the Record sort t whose f field is v. -/
def pListFindOf : PrimId := 291
/-- SetAllBytes(block, v): every byte of block set to v. -/
def pSetAllBytes : PrimId := 288
/-- ParseGoal(cps, goal): the Parse Node of the code points cps with the goal symbol, or ~empty~
where there is none (§5.1.2, by `Model.parse`). -/
def pParseGoal : PrimId := 104
/-- HostReportErrors(errorList): the host's report of errors (§27.2.1 / HTML). -/
def pHostReportErrors : PrimId := 105
/-- PropertyIsKind(P, ~data~ | ~accessor~): whether the own property P is a data or an accessor
property (§6.1.7.1). -/
def pPropertyIsKind : PrimId := 110
/-- §5.2.6 ln(x), log10(x), log2(x): `Model.fn` at `.ln`, `.log10`, `.log2`. -/
def pLn : PrimId := 148
def pLog10 : PrimId := 149
def pLog2 : PrimId := 150
/-- NewSymbol(d): a new Symbol whose [[Description]] is d, a String or *undefined* (§6.1.5). -/
def pNewSymbol : PrimId := 205
/-- NaNEncoding(v, w, p): the host's IEEE 754-2019 encoding of the NaN v in the binary interchange
format of w exponent bits and precision p (§25.1.3.17: any NaN encoding, the same for each NaN). -/
def pNaNEncoding : PrimId := 206
/-- MustCoverChild(node, child): an early error rule of node's production whose condition holds says
child must cover a nonterminal (§5.1.5: no rules apply to child or its descendants). -/
def pMustCoverChild : PrimId := 207
/-- ApproxInteger(x): the host's implementation-approximated integer representing the mathematical
value x (§19.2.5 step 14's radix latitude). -/
def pApproxInteger : PrimId := 208
/-- UnicodeNormalize(s, form): s's code points normalized into the normalization form that form
names (UAX #15), as a String. -/
def pUnicodeNormalize : PrimId := 162
/-- ClosureKind(c, kind): whether the Abstract Closure c's literal is of the kind the enum kind names. -/
def pClosureKind : PrimId := 111
/-- ClosureArity(c): the number of parameters of the Abstract Closure c, by its literal. -/
def pClosureArity : PrimId := 217
/-- RecordFieldNames(r): a new List of the Record's field names, ascending by field id. -/
def pRecordFieldNames : PrimId := 218
/-- MathFn(f, x): "the ( cosine | sine | … ) of x", f the alternative's index: `Model.fn`, or
`Model.sqrt` for the square root. -/
def pMathFn : PrimId := 222
/-- EvaluateBuiltin(F, thisArgument, argumentsList, newTarget): F's behaviour run on the call. -/
def pEvaluateBuiltin : PrimId := 224
/-- HostInitializeBuiltinContext(calleeContext): the host's initialization of a built-in's context. -/
def pHostInitializeBuiltinContext : PrimId := 225
/-- DiscardContextResources(context): the host's release of the context's resources (PrepareForTailCall step 2). -/
def pDiscardContextResources : PrimId := 139
/-- SpinWaitHint(): the host's spin-wait signal, where the environment supports one (Atomics.pause step 1). -/
def pSpinWaitHint : PrimId := 192
/-- AdditionalTimeout(): the host's non-negative addition to a waiter's timeout (DoWait step 23). -/
def pAdditionalTimeout : PrimId := 230
/-- TimeZoneNameSuffix(tv): the host's empty String or " (name)" for a time zone name at tv (TimeZoneString step 9). -/
def pTimeZoneNameSuffix : PrimId := 231
/-- SystemTimeZoneString(): the host's current time zone identifier (SystemTimeZoneIdentifier step 2). -/
def pSystemTimeZoneString : PrimId := 232
/-- TimeNow(): the time value (UTC) identifying the current time. -/
def pTimeNow : PrimId := 233
/-- ParseDateString(s): the host's time value for s, parsed as Date.parse parses it (Date step 4.c.ii.2). -/
def pParseDateString : PrimId := 159
/-- CanAllocate(n, shared): whether the host can create a (Shared, if shared) Data Block of n bytes. -/
def pCanAllocate : PrimId := 185
/-- DebuggerEnabled(): whether an implementation-defined debugging facility is available and enabled. -/
def pDebuggerEnabled : PrimId := 239
/-- DebuggerAction(): an implementation-defined debugging action. -/
def pDebuggerAction : PrimId := 240
/-- NativeFunctionSource(func): an implementation-defined String source code representation of func. -/
def pNativeFunctionSource : PrimId := 241
/-- EscapePattern(pattern, flags): pattern's source text with certain code points escaped. -/
def pEscapePattern : PrimId := 244
/-- HasTimeZoneRules(): whether the implementation includes local political rules for any time zones. -/
def pHasTimeZoneRules : PrimId := 153
/-- AvailableNamedTimeZoneIds(): a new List of the available named time zone identifiers, each once, in
lexicographic code unit order. -/
def pAvailableNamedTimeZoneIds : PrimId := 154
/-- IsNonPrimaryTimeZoneId(id): whether id is a non-primary time zone identifier in this implementation. -/
def pIsNonPrimaryTimeZoneId : PrimId := 155
/-- PrimaryTimeZoneId(id): the primary time zone identifier associated with non-primary identifier `id`. -/
def pPrimaryTimeZoneId : PrimId := 156
/-- SupportsOnlyUTC(): whether the implementation only supports the UTC time zone. -/
def pSupportsOnlyUTC : PrimId := 157
/-- LastTransitionBefore(id, t): the largest integral Number less than t that is a local time of id, or
~empty~. -/
def pLastTransitionBefore : PrimId := 158
/-- toLowercase(cps): `Model.toLower` of the List of code points cps (Unicode §3.13). -/
def pToLowercase : PrimId := 166
/-- SimpleCaseFold(c): `Model.scf?` of the character c, ~empty~ for none (UAX #44 Simple_Case_Folding). -/
def pSimpleCaseFold : PrimId := 170
/-- toUppercase(cps): `Model.toUpper` of the List of code points cps (Unicode §3.13). -/
def pToUppercase : PrimId := 171
/-- scf(c) (§22.2.2.7.3): `Model.scf?` of the code point c, c itself for none. -/
def pScf : PrimId := 179
/-- WaiterListFor(block, i): the agent cluster's WaiterList Record for (block, i). -/
def pWaiterListFor : PrimId := 187
/-- AcquireCriticalSection(wl): wait until no agent is in wl's critical section, then enter it. -/
def pAcquireCriticalSection : PrimId := 188
/-- ReleaseCriticalSection(wl): leave wl's critical section. -/
def pReleaseCriticalSection : PrimId := 190
/-- EnteredCriticalSections(): the WaiterList Records whose critical section the surrounding agent is in. -/
def pEnteredCriticalSections : PrimId := 242
/-- SortStep(n, state, result): the host's next call of a sort's comparator and its state, or the order. -/
def pSortStep : PrimId := 243
/-- ForInStep(obj, history): the host's next action in enumerating obj's properties (EnumerateObjectProperties). -/
def pForInStep : PrimId := 245
/-- IsDataBlock(v): v is a Data Block that is not a Shared Data Block. -/
def pIsDataBlock : PrimId := 112
/-- IsSharedDataBlock(v): v is a Shared Data Block. -/
def pIsSharedDataBlock : PrimId := 113
/-- DesignateShared(block): block, a new Data Block, designated a Shared Data Block. -/
def pDesignateShared : PrimId := 252
/-- TopmostScriptOrModuleContext(): the topmost execution context on the stack whose ScriptOrModule
component is not *null*, or ~empty~ (§9.4.1). -/
def pTopmostScriptOrModuleContext : PrimId := 124
/-- CurrentProduction(): the Parse Node being evaluated, of the innermost running SDO (§9.4.2). -/
def pCurrentProduction : PrimId := 125
/-- PassedArguments(): the List of arguments the running built-in function was passed (§10.3). -/
def pPassedArguments : PrimId := 137
/-- ContextBelowTop(): the second to top element of the execution context stack, or ~empty~ (§27.6.3.8). -/
def pContextBelowTop : PrimId := 197
/-- OnContextStack(ctx): whether ctx is an element of the execution context stack (RunSuspendedContext step 5). -/
def pOnContextStack : PrimId := 264
/-- HostGlobalObject(realm): the object the host requires as realm's global object, else ~empty~ (InitializeHostDefinedRealm step 10). -/
def pHostGlobalObject : PrimId := 234
/-- HostThisValue(realm): the object the host requires as realm's global `this`, else ~empty~ (InitializeHostDefinedRealm step 12). -/
def pHostThisValue : PrimId := 235
/-- HostGlobalProperties(realm, global): the host's global object properties (InitializeHostDefinedRealm step 17). -/
def pHostGlobalProperties : PrimId := 236
/-- HostReportCleanupError(completion): the host's report of a cleanup job's error (HostEnqueueFinalizationRegistryCleanupJob step 2). -/
def pHostReportCleanupError : PrimId := 237
/-- MayCleanup(registry): ~empty~, or the cell the implementation cleans up next (CleanupFinalizationRegistry step 3). -/
def pMayCleanup : PrimId := 238
/-- HostJobCallbackData(callback): the [[HostDefined]] of the JobCallback Record HostMakeJobCallback makes. -/
def pHostJobCallbackData : PrimId := 265
/-- HostPrepareCallJobCallback(jobCallback): the host's steps before HostCallJobCallback's Call. -/
def pHostPrepareCallJobCallback : PrimId := 266
/-- HostCleanupCallJobCallback(jobCallback): the host's steps after HostCallJobCallback's Call. -/
def pHostCleanupCallJobCallback : PrimId := 267
/-- ReplacedSourceText(n, t): the source text of n's parse with n's own replaced by t (Annex B.3.2's replacing). -/
def pReplacedSourceText : PrimId := 268
/-- SwitchToAgent(a): park the surrounding agent's execution context stack and install the Agent Record a's. -/
def pSwitchToAgent : PrimId := 269
/-- HostSelectAgent(a, n): the agent the host runs next after a, with n events in a's [[EventList]], or ~empty~. -/
def pHostSelectAgent : PrimId := 270
/-- AgentTimeout(): the time the host advances the clock to while no agent can run. -/
def pAgentTimeout : PrimId := 271
/-- AgentWoken(): whether the surrounding agent, suspended by SuspendAgentUntil, has been woken. -/
def pAgentWoken : PrimId := 272
/-- WakeAgent(sig): wake the agent with the agent signifier sig from SuspendAgentUntil. -/
def pWakeAgent : PrimId := 191
/-- SetEvaluationSteps(n, c): c the steps n's evaluation performs from now on (Annex B.3.2). -/
def pSetEvaluationSteps : PrimId := 273
/-- EvaluationStepsOf(n): the steps the last SetEvaluationSteps of n gave, or ~empty~. -/
def pEvaluationStepsOf : PrimId := 274
/-- ChooseReadsBytesFrom(ex, er, block, i, n): the write events a shared read of n bytes of block from i reads from. -/
def pChooseReadsBytesFrom : PrimId := 275
/-- AgentNextJob(): the surrounding agent's next job, its scheduling's log position, or ~empty~. -/
def pAgentNextJob : PrimId := 276
/-- AgentPrepareJob(k): the preparation steps of the job scheduled at k; that Job Abstract Closure. -/
def pAgentPrepareJob : PrimId := 277
/-- AgentCleanupJob(k): the cleanup steps of the job scheduled at k. -/
def pAgentCleanupJob : PrimId := 278
/-- NumberDigitsExponent(x, radix): Number::toString step 5's n for x and radix (the model's `numDigits`). -/
def pNumberDigitsExponent : PrimId := 292
/-- NumberDigitsCount(x, radix): Number::toString step 5's k for x and radix. -/
def pNumberDigitsCount : PrimId := 293
/-- NumberDigitsSignificand(x, radix): Number::toString step 5's s for x and radix. -/
def pNumberDigitsSignificand : PrimId := 294
/-- DecimalExponent(x): the integer e with 10^e ≤ x < 10^(e+1), for x > 0 (the model's `decExp`). -/
def pDecimalExponent : PrimId := 295
/-- YearFromTimeOf(tv): the largest integer y with TimeFromYear(y) ≤ tv (§21.4.1.7). -/
def pYearFromTimeOf : PrimId := 281
/-- FirstDayOf(y, m): the least time value whose year is y, month m and date 1, or NaN (§21.4.1.28 step 8). -/
def pFirstDayOf : PrimId := 282
/-- ApproxPower(base, exponent): the host's implementation-approximated Number value representing ℝ(base) raised to
the ℝ(exponent) power (Number::exponentiate step 13). -/
def pApproxPower : PrimId := 283
/-- BigIntTooLarge(operation, x, y): whether the BigInt the BigInt method named operation returns for x and y would
exceed the implementation's maximum BigInt size (erratum BigIntMaximumSize). -/
def pBigIntTooLarge : PrimId := 284
/-- StringTooLarge(len): whether a String of length len exceeds the implementation's maximum String length
(erratum StringMaximumLength). -/
def pStringTooLarge : PrimId := 306

/-- ClauseProperties(o, c): the own properties clause c specifies for o, as property Records. -/
def pClauseProperties : PrimId := 122
/-- RealmIntrinsic(realm, n): the object realm.[[Intrinsics]] records under the intrinsic name n (§6.1.7.4). -/
def pRealmIntrinsic : PrimId := 132
/-- IntrinsicObjects(): the built-in objects of clauses 19-28, as Records in a creation order (§9.3.2 step 2). -/
def pIntrinsicObjects : PrimId := 226
/-- PropertyOrder(o, ps): a permutation of the List ps, the order o's properties are created in (§9.3.2 step 2). -/
def pPropertyOrder : PrimId := 227
/-- OmitSharedArrayBuffer(): whether the host omits the global object's "SharedArrayBuffer" property (§25.2.2). -/
def pOmitSharedArrayBuffer : PrimId := 228
/-- SetFieldNamed(r, f, v): sets r's field or internal slot named f to v. -/
def pSetFieldNamed : PrimId := 247
/-- HostSupportsOptional(c): whether a host that is not a web browser provides the optional feature clause c specifies. -/
def pHostSupportsOptional : PrimId := 248
/-- IsIntrinsicName(n): whether n is this specification's name of an intrinsic object (§6.1.7.4). -/
def pIsIntrinsicName : PrimId := 249
/-- WellKnownSymbol(d): the well-known symbol whose [[Description]] is d (§6.1.5.1). -/
def pWellKnownSymbol : PrimId := 251
/-- LocaleUppercase(cps): the host locale's upper-case mapping of cps (String.prototype.toLocaleUpperCase). -/
def pLocaleUppercase : PrimId := 253
/-- LocaleLowercase(cps): the host locale's lower-case mapping of cps (String.prototype.toLocaleLowerCase). -/
def pLocaleLowercase : PrimId := 254
/-- LocaleCompare(a, b): the host's locale-sensitive comparison of a with b (String.prototype.localeCompare). -/
def pLocaleCompare : PrimId := 255
/-- LocaleNumberString(x): the host locale's String for the Number or BigInt x, or ~empty~ for toString's. -/
def pLocaleNumberString : PrimId := 256
/-- LocaleDateString(k, v): the host locale's String for the Date v's portion k, ~empty~ for the non-locale form, or ~throw~. -/
def pLocaleDateString : PrimId := 258
/-- SuspendAgentUntil(wl, t): suspend the surrounding agent until the time is t or a NotifyWaiter on wl wakes it. -/
def pSuspendAgentUntil : PrimId := 259
/-- ExpandedYearForm(tv): whether toISOString writes the year of tv, one from 0 to 9999, as an expanded year. -/
def pExpandedYearForm : PrimId := 261
/-- HostExtendIntrinsics(realm): the host's additional properties of the objects that exist, after CreateIntrinsics (InitializeHostDefinedRealm step 2). -/
def pHostExtendIntrinsics : PrimId := 262
/-- HostExtendObject(o): the host's additional own properties of the object o the steps have just created. -/
def pHostExtendObject : PrimId := 263

/-- Phrases the machine uses: "a newly created *E* object". -/
def phNewError : PhraseId := 0
/-- "_s_'s F" (prim Component): a place in `Set _ctx_'s LexicalEnvironment to …`. -/
def phPoss : PhraseId := 22
/-- "the F component of _s_" (prim Component): a place in `Set the Generator component of _genContext_ to …`. -/
def phComponentOf : PhraseId := 237

def sdoEarlyErrors : SdoId := 0

/-- `the |X| of n` through n's unit chain. -/
def erUnitChainChild : ErratumId := 0
/-- A lookahead reads past the inserted semicolons. -/
def erLookaheadSourceTokens : ErratumId := 3
/-- B.1.1's |HTMLCloseComment| input element is a comment. -/
def erHTMLCloseCommentToken : ErratumId := 4
/-- B.1.2's ordered alternatives as commitment. -/
def erAnnexBRegExpOrder : ErratumId := 5
/-- B.1.2's group count read from a committed parse with the condition true. -/
def erAnnexBGroupCount : ErratumId := 6
/-- A covered node's parent is its cover's parent. -/
def erCoveredNodeParent : ErratumId := 8
end Known

/-- The enum of ClosureKind that names a literal's kind; none for "a new Abstract Closure". -/
def CloKind.enumId : CloKind → Option EnumId
  | .abstract => none
  | .job => some Known.eJob
  | .matcher => some Known.eMatcher
  | .matcherContinuation => some Known.eMatcherContinuation
  | .readModifyWrite => some Known.eReadModifyWrite

/-- A field written as an expression, as a place: its field and subject. `the F of _s_`, and the
phrases of prim Component `_s_'s F` and `the F component of _s_` (kept as phrases for printing). -/
def Expr.fieldPlace? : Expr → Option (FieldId × Expr)
  | .component f _ s => some (f, s)
  | .phrase p [.e s, .field f] => if p == Known.phPoss then some (f, s) else none
  | .phrase p [.field f, .e s] => if p == Known.phComponentOf then some (f, s) else none
  | _ => none

end Ecma
