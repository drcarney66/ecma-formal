module

public import Ecma.Machine.CodeTable

@[expose] public section

/-!
# Expressions, conditions, predicates and types as operand trees

`linE`, `linC`, `linP`, `linT` and `linH`, in the steps' evaluation order (a leaf's or a call's operands left to
right, then the operation): a predicate's or a type's subject is the bound value.
-/

namespace Ecma.Machine
open Ecma

/-! `lin`: the expanded program's units as the machine's code. -/

/-- What `lin` reads: the program, and the frame's closure literals. -/
structure Cx where
  P : Prog
  clos : Array CloLit := #[]

/-- The predicates after the first, from the answer `acc` (`predRest`): left to right. -/
def restOp (acc : Op) : List (Conj × Op) → Op
  | [] => acc
  | (.and, p) :: r => restOp (.and [acc, p]) r
  | (.or, p) :: r => restOp (.or [acc, p]) r

section Lin
variable (cx : Cx)

mutual
/-- An expression. -/
def linE : Expr → Op
  | .var x => .var x
  | .val v => .const (.val v)
  | .math sg m => .const (.math sg m)
  | .enum e => .const (.enum e)
  | .param p => .const (.param p)
  | .intrinsic i => .leaf (.intrinsic i) []
  | .fieldName f => .const (.fieldName f)
  | .nt k as => .const (.nt k as)
  | .prod ps _ => .const (.prod ps)
  | .codeUnit n _ _ => .const (.nat n)
  | .codePoint n _ _ => .const (.nat n)
  | .code s _ => .const (.str s)
  | .term s => .const (.term s)
  | .call (.alg a) args => .call (.alg a) (linEs args)
  | .call (.prim p) args => .call (.prim p) (linEs args)
  | .callAt a args => .call (.callAt a) (linEs args)
  | .sdo s _ e args => .on (.sdo s) (linE e) (linEs args)
  | .component f _ e => .leaf (.field f) [linE e]
  | .field e f => .leaf (.field f) [linE e]
  | .imethod e m args => .on (.imethod m) (linE e) (linEs args)
  | .cmethod e m args => .on (.cmethod m) (linE e) (linEs args)
  | .apply f args => .on .apply (linE f) (linEs args)
  | .index e i => .leaf .index [linE e, linE i]
  | .q e => .leaf .q [linE e]
  | .bang e => .leaf .bang [linE e]
  | .bangAt r e => .leaf (.bangAt r) [linE e]
  | .erratum r s e => .erratum r s (linE e)
  | .un o e => .leaf (.un o) [linE e]
  | .bin o a b => .leaf (.bin o) [linE a, linE b]
  | .paren e => linE e
  | .list es => .leaf .list (linEs es)
  | .record _ k fs => .leaf (.record k (fs.map (·.1))) (linFs fs)
  | .annot _ e => linE e
  | .xref x => match x.clause with
    | some c => .const (.clause c)
    | none => .stop .sortError
  | .closure site => match cx.clos[site]? with
    | some cl => .closure site cl.caps
    | none => .stop .sortError
  | .table t _ => .const (.table t)
  | .definition x _ => match x.clause with
    | some c => .const (.alg ⟨c, 0⟩)
    | none => .stop .sortError
  | .tableStep t k _ => .call (.tstep t) [linE k]
  | .extreme .. => .residue "extreme"
  | .phrase .. => .residue "phrase"
  | .prose ch ps => match ch.live? with
    | some q => .call (.prim q) (linParts ps)
    | none => .residue "prose"
  | .resumedWith _ => .resumed
  | .thisNode => .node
  | .child k nt _ => .child k nt
  | .childOf e nt _ => .leaf (.childOf nt) [linE e]
  | .thisValue _ => .var 0
  | .newTarget => .var 1
  | .bnd x => .bnd x
  | .data d => .const (.data d)
  | .ofCond c => linC c

def linEs : List Expr → List Op
  | [] => []
  | e :: es => linE e :: linEs es

def linF : FieldId × Expr → Op
  | (_, e) => linE e

def linFs : List (FieldId × Expr) → List Op
  | [] => []
  | fe :: fs => linF fe :: linFs fs

/-- A phrase's arguments: a spreading phrase's list hole's elements in its place, a variable as a binder. -/
def linArgs (p : PhraseId) (hs : List Hole) : List Op :=
  if (cx.P.phrase p).spreads then linSpread hs else linPhArgs hs

/-- Holes as a phrase's arguments (`Hole.phraseArg`). -/
def linPhArgs : List Hole → List Op
  | [] => []
  | .e (.var x) :: hs => .bnd x :: linPhArgs hs
  | h :: hs => linH h :: linPhArgs hs

/-- Holes as a spreading phrase's arguments (`Hole.spreadArgs`). -/
def linSpread : List Hole → List Op
  | [] => []
  | .l _ xs :: hs => linEs xs ++ linSpread hs
  | .e (.var x) :: hs => .bnd x :: linSpread hs
  | h :: hs => linH h :: linSpread hs

/-- A prose's holes, in order. -/
def linParts : List Part → List Op
  | [] => []
  | .text _ :: ps => linParts ps
  | .hole h :: ps => linH h :: linParts ps

/-- A hole's value; a type or condition value is not the machine's data, residue. -/
def linH : Hole → Op
  | .e x => linE x
  | .c x => linC x
  | .t (.sort _ [] s _) => .const (.data (.sort s))
  | .t _ => .residue "tyHole"
  | .b x => .bnd x
  | .bc .. => .residue "condHole"
  | .w i => .const (.data (.choice i))
  | .l _ xs => .leaf .list (linEs xs)
  | .text s => .const (.str s)
  | .field f => .const (.fieldName f)

/-- A condition, a Boolean; a predicate chain's answer checked a Boolean. -/
def linC : Cond → Op
  | .preds e p rest => .bind (linE e) (.and [restOp (linP p) (linRest rest)])
  | .rel o a b => .leaf (.rel o) [linE a, linE b]
  | .and _ cs => .and (linCs cs)
  | .or _ cs => .or (linCs cs)
  | .paren c => linC c
  | .alg a => .leaf .toBool [.call (.callAt a) []]
  | .phrase .. => .residue "phrase"
  | .prose ch ps => .leaf .toBool [match ch.live? with
    | some q => .call (.prim q) (linParts ps)
    | none => .residue "prose"]
  | .expr e => .leaf .toBool [linE e]
  | .pass _ => .residue "pass"

def linCs : List Cond → List Op
  | [] => []
  | c :: cs => linC c :: linCs cs

/-- A predicate of the bound subject, a Boolean. -/
def linP : Pred → Op
  | .isVal neg f vs => .leaf (.isVal neg (f == .neither)) (.bound :: linEs vs)
  | .isTy neg f ts => .leaf (.isTy neg (f == .neither)) [.bind (.leaf .used [.bound]) (.or (linTs ts))]
  | .phrase .. => .residue "phrase"
  | .call (.alg a) args neg => .leaf (.isTy neg false) [.call (.alg a) (linEs args ++ [.bound])]
  | .call (.prim q) args neg => .leaf (.isTy neg false) [.call (.prim q) (linEs args ++ [.bound])]

def linR : Conj × Pred → Conj × Op
  | (j, p) => (j, linP p)

def linRest : List (Conj × Pred) → List (Conj × Op)
  | [] => []
  | r :: rs => linR r :: linRest rs

/-- The bound subject's membership in a type, a Boolean. -/
def linT : TyExpr → Op
  | .sort _ mods s _ => sortsOp mods s
  | .listOf _ t => .all .bound (linT t)
  | .union _ _ ts => .or (linTs ts)
  | .value e => .call .tyEq [linE e, .bound]
  | .var _ x => .call .tyEq [.var x, .bound]
  | .interval t lo hi =>
    .and [linT t, .leaf .both [.leaf (.rel .le) [linE lo, .bound], .leaf (.rel .le) [.bound, linE hi]]]
  | .nt _ k _ => .leaf (.tyNt k) [.bound]
  | .that t p rest => .and [linT t, restOp (linP p) (linRest rest)]
  | .phrase .. => .residue "phrase"
  | .pred p => linP p
  | .completion _ => .residue "completion"
  | .record _ => .residue "record"
  | .prose _ => .residue "prose"

def linTs : List TyExpr → List Op
  | [] => []
  | t :: ts => linT t :: linTs ts
end

end Lin

end Ecma.Machine
