module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# An equation names one value

An SDO's equation row (`RowForm.equation`) states what the operation's value is: "The TV of
|TemplateCharacters| … is *undefined* if the TV of |TemplateCharacter| is *undefined* or the TV of
|TemplateCharacters| is *undefined*. Otherwise, it is the string-concatenation of the TV of
|TemplateCharacter| and the TV of |TemplateCharacters|." Each "the TV of |X|" in it names one value, however
often it is written. `SdoRow.bindApplications` reads an equation so: each application of an SDO without
arguments to a child that the row writes more than once is evaluated once, by a `Let` before the row's own
steps, and each occurrence reads the variable. The static SDOs that equations define have no effects, so the
value is the same; the data keeps the row as written.
-/

namespace Ecma.Equations

/-- An SDO applied without arguments to a child of the row's Parse Node: the SDO and the child. -/
abbrev Key := SdoId × Nat × NtId × String

mutual
/-- The applications in `e`, in order, with their repetitions. -/
def Expr.keys : Expr → List Key
  | .sdo s _ (.child k n x) [] => [(s, k, n, x)]
  | .sdo _ _ e as => Expr.keys e ++ Expr.keysL as
  | .call _ as => Expr.keysL as
  | .bin _ a b => Expr.keys a ++ Expr.keys b
  | .un _ e => Expr.keys e
  | .paren e => Expr.keys e
  | .list es => Expr.keysL es
  | .phrase _ hs => Hole.keysL hs
  | _ => []

def Expr.keysL : List Expr → List Key
  | [] => []
  | e :: es => Expr.keys e ++ Expr.keysL es

def Hole.keys : Hole → List Key
  | .e x => Expr.keys x
  | .c x => Cond.keys x
  | .l _ xs => Expr.keysL xs
  | _ => []

def Hole.keysL : List Hole → List Key
  | [] => []
  | h :: hs => Hole.keys h ++ Hole.keysL hs

def Cond.keys : Cond → List Key
  | .preds e _ _ => Expr.keys e
  | .rel _ a b => Expr.keys a ++ Expr.keys b
  | .and _ cs => Cond.keysL cs
  | .or _ cs => Cond.keysL cs
  | .paren c => Cond.keys c
  | .phrase _ hs => Hole.keysL hs
  | .expr e => Expr.keys e
  | _ => []

def Cond.keysL : List Cond → List Key
  | [] => []
  | c :: cs => Cond.keys c ++ Cond.keysL cs
end

section Sub
variable (m : List (Key × Slot))

mutual
/-- `e` with each application of `m` read from its variable. -/
def Expr.sub : Expr → Expr
  | .sdo s a (.child k n x) [] => match m.lookup (s, k, n, x) with
    | some v => .var v
    | none => .sdo s a (.child k n x) []
  | .sdo s a e as => .sdo s a (Expr.sub e) (Expr.subL as)
  | .call f as => .call f (Expr.subL as)
  | .bin o a b => .bin o (Expr.sub a) (Expr.sub b)
  | .un o e => .un o (Expr.sub e)
  | .paren e => .paren (Expr.sub e)
  | .list es => .list (Expr.subL es)
  | .phrase p hs => .phrase p (Hole.subL hs)
  | e => e

def Expr.subL : List Expr → List Expr
  | [] => []
  | e :: es => Expr.sub e :: Expr.subL es

def Hole.sub : Hole → Hole
  | .e x => .e (Expr.sub x)
  | .c x => .c (Cond.sub x)
  | .l f xs => .l f (Expr.subL xs)
  | h => h

def Hole.subL : List Hole → List Hole
  | [] => []
  | h :: hs => Hole.sub h :: Hole.subL hs

def Cond.sub : Cond → Cond
  | .preds e p rest => .preds (Expr.sub e) p rest
  | .rel o a b => .rel o (Expr.sub a) (Expr.sub b)
  | .and f cs => .and f (Cond.subL cs)
  | .or f cs => .or f (Cond.subL cs)
  | .paren c => .paren (Cond.sub c)
  | .phrase p hs => .phrase p (Hole.subL hs)
  | .expr e => .expr (Expr.sub e)
  | c => c

def Cond.subL : List Cond → List Cond
  | [] => []
  | c :: cs => Cond.sub c :: Cond.subL cs
end

end Sub

/-- A `Return`'s applications. -/
def Stmt.retKeys : Stmt → List Key
  | .ret (some e) => Expr.keys e
  | _ => []

/-- An equation's statement's applications: its returned value's, or an `If`'s condition's and its two
`Return`s'. -/
def Stmt.keys : Stmt → List Key
  | .ret (some e) => Expr.keys e
  | .if_ c (.inline s) [] els => Cond.keys c ++ Stmt.retKeys s ++ match els with
    | some (.mk _ none (.inline t)) => Stmt.retKeys t
    | _ => []
  | _ => []

/-- A `Return` with each application of `m` read from its variable. -/
def Stmt.retSub (m : List (Key × Slot)) : Stmt → Stmt
  | .ret (some e) => .ret (some (Expr.sub m e))
  | s => s

/-- `s` with each application of `m` read from its variable, where `Stmt.keys` finds them. -/
def Stmt.sub (m : List (Key × Slot)) : Stmt → Stmt
  | .ret (some e) => .ret (some (Expr.sub m e))
  | .if_ c (.inline s) [] els => .if_ (Cond.sub m c) (.inline (Stmt.retSub m s)) [] (match els with
    | some (.mk as none (.inline t)) => some (.mk as none (.inline (Stmt.retSub m t)))
    | a => a)
  | s => s

/-- The applications written more than once, in the order of their first occurrence. -/
def repeated (ks : List Key) : List Key :=
  (ks.filter fun k => (ks.filter (· == k)).length ≥ 2).eraseDups

end Ecma.Equations

namespace Ecma
open Equations

/-- An equation row with each application of an SDO without arguments to a child that it writes more than once
evaluated once: a `Let` of a new variable for each, in the order of their first occurrence, before the row's
steps, which read the variable in its place. Any other row as it is. -/
def SdoRow.bindApplications (r : SdoRow) : SdoRow :=
  if r.form != .equation then r else
  let ks := repeated (r.body.flatMap fun | .mk _ s => Stmt.keys s)
  if ks.isEmpty then r else
  let m := ks.zipIdx.map fun (k, i) => (k, r.vars.size + i)
  let lets := m.map fun ((s, k, n, x), v) => Node.mk [] (.let_ v (.sdo s .the (.child k n x) []))
  { r with vars := r.vars ++ (m.map fun (_, v) => s!"value{v - r.vars.size}").toArray,
           body := lets ++ r.body.map fun | .mk as s => .mk as (Stmt.sub m s) }

end Ecma
