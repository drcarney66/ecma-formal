module

public import Ecma.Machine.CodeTable

@[expose] public section

/-!
# Expressions, conditions, predicates and types as operand trees

`linE`, `linC`, `linP`, `linT`, in the steps' evaluation order (a leaf's or a call's operands left to
right, then the operation): a predicate's or a type's subject is the bound value.
-/

namespace Ecma.Machine
open Ecma

/-! `lin`: the program's units as the machine's code. -/

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
  | .prod ps => .const (.prod ps)
  | .codeUnit n _ _ => .const (.nat n)
  | .codePoint n _ _ => .const (.nat n)
  | .code s => .const (.str s)
  | .term s => .const (.term s)
  | .call (.alg a) args => .call (.alg a) (linEs args)
  | .call (.prim p) args => .call (.prim p) (linEs args)
  | .callAt a args => .call (.callAt a) (linEs args)
  | .sdo s e args => .on (.sdo s) (linE e) (linEs args)
  | .component f e => .leaf (.field f) [linE e]
  | .field e f => .leaf (.field f) [linE e]
  | .imethod e m args => .on (.imethod m) (linE e) (linEs args)
  | .cmethod e m args => .on (.cmethod m) (linE e) (linEs args)
  | .apply f args => .on .apply (linE f) (linEs args)
  | .index e i => .leaf .index [linE e, linE i]
  | .q e => .leaf .q [linE e]
  | .bang e => .leaf .bang [linE e]
  | .un o e => .leaf (.un o) [linE e]
  | .bin o a b => .leaf (.bin o) [linE a, linE b]
  | .paren e => linE e
  | .list es => .leaf .list (linEs es)
  | .record k fs => .leaf (.record k (fs.map (·.1))) (linFs fs)
  | .xref c => .const (.clause c)
  | .closure site => match cx.clos[site]? with
    | some cl => .closure site cl.caps
    | none => .stop .sortError
  | .table t => .const (.table t)
  | .definition c => .const (.alg ⟨c, 0⟩)
  | .tableStep t k => .call (.tstep t) [linE k]
  | .resumedWith _ => .resumed
  | .thisNode => .node
  | .child k nt => .child k nt
  | .childOf e nt => .leaf (.childOf nt) [linE e]
  | .thisValue => .var 0
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

/-- A condition, a Boolean; a predicate chain's answer checked a Boolean. -/
def linC : Cond → Op
  | .preds e p rest => .bind (linE e) (.and [restOp (linP p) (linRest rest)])
  | .rel o a b => .leaf (.rel o) [linE a, linE b]
  | .and cs => .and (linCs cs)
  | .or cs => .or (linCs cs)
  | .paren c => linC c
  | .alg a => .leaf .toBool [.call (.callAt a) []]
  | .expr e => .leaf .toBool [linE e]
  | .pass _ => .residue "pass"

def linCs : List Cond → List Op
  | [] => []
  | c :: cs => linC c :: linCs cs

/-- A predicate of the bound subject, a Boolean. -/
def linP : Pred → Op
  | .isVal neg nei vs => .leaf (.isVal neg nei) (.bound :: linEs vs)
  | .isTy neg nei ts => .leaf (.isTy neg nei) [.bind (.leaf .used [.bound]) (.or (linTs ts))]
  | .call (.alg a) args neg => .leaf (.isTy neg false) [.call (.alg a) (linEs args ++ [.bound])]
  | .call (.prim q) args neg => .leaf (.isTy neg false) [.call (.prim q) (linEs args ++ [.bound])]

def linR : Conj × Pred → Conj × Op
  | (j, p) => (j, linP p)

def linRest : List (Conj × Pred) → List (Conj × Op)
  | [] => []
  | r :: rs => linR r :: linRest rs

/-- The bound subject's membership in a type, a Boolean. -/
def linT : TyExpr → Op
  | .sort mods s => sortsOp mods s
  | .listOf t => .all .bound (linT t)
  | .seqOf _ => .residue "seqOf"
  | .butNot _ _ => .residue "butNot"
  | .doc _ => .residue "doc"
  | .union ts => .or (linTs ts)
  | .value e => .call .tyEq [linE e, .bound]
  | .var x => .call .tyEq [.var x, .bound]
  | .interval t lo hi =>
    .and [linT t, .leaf .both [.leaf (.rel .le) [linE lo, .bound], .leaf (.rel .le) [.bound, linE hi]]]
  | .nt k => .leaf (.tyNt k) [.bound]
  | .that t p rest => .and [linT t, restOp (linP p) (linRest rest)]
  | .pred p => linP p
  | .completion _ => .residue "completion"
  | .record _ => .residue "record"

def linTs : List TyExpr → List Op
  | [] => []
  | t :: ts => linT t :: linTs ts
end

end Lin

end Ecma.Machine
