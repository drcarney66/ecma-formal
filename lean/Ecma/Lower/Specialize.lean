module

public import Ecma.Ops.ProgPrim
public import Ecma.Lower.Sites
public import Ecma.Notation.AlgKey

@[expose] public section

/-!
# Specializing the phrases that take code

A phrase whose meaning is an overlay algorithm `g` may be given a condition (`.bc`) or a type that is
not a bare sort (`.t`): a hole whose value is code. This pass rewrites each such site so that no hole
is code:
- a condition becomes an Abstract Closure literal appended to the caller (its parameters the
  condition's binders, its captures the other variables it reads, its steps `Return c`), or in an
  early-error rule, which has no closures, the `definition` of a capture-free algorithm;
- a site with types becomes a site of a copy of `g` (a fresh phrase and algorithm) whose `is a _t_`
  tests are tests of a fresh type phrase, the type's hole a choice;
- `a new T` of a sort with modifiers becomes a phrase of NewRecord on the sort and its modifiers.

`GFrag`, `CFrag`, `TFrag`: the decided premises (the phrase algorithm, the condition, the type).
`Tables.site`: a site's rewrite. `Decl.declare`: the declarations the rewrite refers to, added to a
program; `Tables.rewrite`: the declared program with its sites rewritten, a table's as an early-error rule's.
-/

namespace Ecma.Spec

/-- A hole whose value is code: a condition, or a type other than a bare sort. -/
def Hole.code : Hole → Bool
  | .bc .. => true
  | .t (.sort _ [] _ _) => false
  | .t _ => true
  | _ => false

/-- How a phrase algorithm may read a slot: freely, only applied to `k` arguments, only as a type. -/
inductive Use where
  | free
  | apply (k : Nat)
  | ty
  deriving BEq, Inhabited

def Use.isFree : Use → Bool
  | .free => true
  | _ => false

/-- The use a site's holes allow of the phrase algorithm's slot `y`. -/
def useOf (hs : List Hole) (y : Slot) : Use :=
  match hs[y]? with
  | some (.bc xs _) => .apply xs.length
  | some (.t (.sort _ [] _ _)) => .free
  | some (.t _) => .ty
  | _ => .free

section G
variable (u : Slot → Use)

mutual
/-- A type that reads a slot used as a type. -/
def GFrag.tyT : TyExpr → Bool
  | .var _ y => u y == .ty
  | .union _ _ ts => GFrag.tyTs ts
  | _ => false

def GFrag.tyTs : List TyExpr → Bool
  | [] => false
  | t :: ts => GFrag.tyT t || GFrag.tyTs ts
end

/-- A predicate that reads a slot used as a type. -/
def GFrag.tyP : Pred → Bool
  | .isTy _ _ ts => GFrag.tyTs u ts
  | _ => false

/-- Predicates that read a slot used as a type. -/
def GFrag.tyRest : List (Conj × Pred) → Bool
  | [] => false
  | (_, p) :: r => GFrag.tyP u p || GFrag.tyRest r

mutual
/-- The phrase algorithm's expressions: its code slots read only as `u` allows; no closure,
table step, binding expression or hole that is code. -/
def GFrag.e : Expr → Bool
  | .var y => (u y).isFree
  | .val _ | .math .. | .enum _ | .fieldName _ | .nt .. | .term _ | .code .. | .intrinsic _ | .param _ => true
  | .call _ as => GFrag.es as
  | .sdo _ _ e as => GFrag.e e && GFrag.es as
  | .component _ _ e => GFrag.e e
  | .field e _ => GFrag.e e
  | .index e i => GFrag.e e && GFrag.e i
  | .apply (.var c) as => (match u c with
      | .apply k => as.length == k
      | .free => true
      | .ty => false) && GFrag.es as
  | .apply f as => GFrag.e f && GFrag.es as
  | .bin _ a b => GFrag.e a && GFrag.e b
  | .un _ e => GFrag.e e
  | .paren e => GFrag.e e
  | .q e => GFrag.e e
  | .bang e => GFrag.e e
  | .list es => GFrag.es es
  | .phrase _ hs => GFrag.hs hs
  | _ => false

def GFrag.es : List Expr → Bool
  | [] => true
  | e :: es => GFrag.e e && GFrag.es es

def GFrag.p : Pred → Bool
  | .isVal _ _ vs => GFrag.es vs
  | .isTy _ _ ts => GFrag.ts ts
  | .phrase _ hs => GFrag.hs hs
  | .call _ as _ => GFrag.es as

def GFrag.rest : List (Conj × Pred) → Bool
  | [] => true
  | (_, p) :: r => GFrag.p p && GFrag.rest r

/-- The phrase algorithm's conditions: a subject tested as a type slot is a variable. -/
def GFrag.c : Cond → Bool
  | .preds e p rest => GFrag.e e && GFrag.p p && GFrag.rest rest &&
      (e.slot?.isSome || !(GFrag.tyP u p || GFrag.tyRest u rest))
  | .rel _ a b => GFrag.e a && GFrag.e b
  | .and _ cs => GFrag.cs cs
  | .or _ cs => GFrag.cs cs
  | .paren c => GFrag.c c
  | .phrase _ hs => GFrag.hs hs
  | .expr e => GFrag.e e
  | _ => false

def GFrag.cs : List Cond → Bool
  | [] => true
  | c :: cs => GFrag.c c && GFrag.cs cs

def GFrag.t : TyExpr → Bool
  | .sort .. | .nt .. => true
  | .union _ _ ts => GFrag.ts ts
  | .var _ y => u y == .ty || (u y).isFree
  | .phrase _ hs => GFrag.hs hs
  | _ => false

def GFrag.ts : List TyExpr → Bool
  | [] => true
  | t :: ts => GFrag.t t && GFrag.ts ts

def GFrag.h : Hole → Bool
  | .e x => GFrag.e x
  | .c x => GFrag.c x
  | .b y => (u y).isFree
  | .t (.sort _ [] _ _) | .w _ | .text _ | .field _ => true
  | .l _ xs => GFrag.es xs
  | _ => false

def GFrag.hs : List Hole → Bool
  | [] => true
  | h :: hs => GFrag.h h && GFrag.hs hs

def GFrag.s : Stmt → Bool
  | .let_ x e => (u x).isFree && GFrag.e e
  | .set (.var x) e => (u x).isFree && GFrag.e e
  | .ret none => true
  | .ret (some e) => GFrag.e e
  | .perform e => GFrag.e e
  | .if_ c b arms els => GFrag.c c && GFrag.b b && GFrag.arms arms && GFrag.els els
  | .assert c => GFrag.c c
  | .forEach x none l _ b => (u x).isFree && GFrag.e l && GFrag.b b
  | .forEach x (some t) l _ b => (u x).isFree && GFrag.t t && GFrag.e l && GFrag.b b
  | .forRange x lo _ hi _ _ b => (u x).isFree && GFrag.e lo && GFrag.e hi && GFrag.b b
  | .forKeys x o c _ b => (u x).isFree && GFrag.e o && GFrag.c c && GFrag.b b
  | .mutate _ hs => GFrag.hs hs
  | .phrase _ hs => GFrag.hs hs
  | _ => false

def GFrag.b : Body → Bool
  | .inline s => GFrag.s s
  | .block ns => GFrag.ns ns

def GFrag.ns : List Node → Bool
  | [] => true
  | .mk _ s :: ns => GFrag.s s && GFrag.ns ns

def GFrag.arms : List Arm → Bool
  | [] => true
  | a :: as => GFrag.arm a && GFrag.arms as

def GFrag.arm : Arm → Bool
  | .mk _ (some c) b => GFrag.c c && GFrag.b b
  | .mk _ none b => GFrag.b b

def GFrag.els : Option Arm → Bool
  | none => true
  | some a => GFrag.arm a
end

end G

section T

mutual
/-- A type a fresh type phrase tests: no variable, closure, table step or hole that is code. -/
def TFrag.t : TyExpr → Bool
  | .sort .. | .nt .. => true
  | .union _ _ ts => TFrag.ts ts
  | .listOf _ t => TFrag.t t
  | .that t p rest => TFrag.t t && TFrag.p p && TFrag.rest rest
  | .phrase _ hs => TFrag.hs hs
  | _ => false

def TFrag.ts : List TyExpr → Bool
  | [] => true
  | t :: ts => TFrag.t t && TFrag.ts ts

def TFrag.p : Pred → Bool
  | .isVal _ _ vs => TFrag.es vs
  | .isTy _ _ ts => TFrag.ts ts
  | .phrase _ hs => TFrag.hs hs
  | _ => false

def TFrag.rest : List (Conj × Pred) → Bool
  | [] => true
  | (_, p) :: r => TFrag.p p && TFrag.rest r

def TFrag.e : Expr → Bool
  | .val _ | .math .. | .enum _ | .fieldName _ | .code .. | .term _ | .nt .. | .intrinsic _ => true
  | .phrase _ hs => TFrag.hs hs
  | _ => false

def TFrag.es : List Expr → Bool
  | [] => true
  | e :: es => TFrag.e e && TFrag.es es

def TFrag.h : Hole → Bool
  | .e x => TFrag.e x
  | .t (.sort _ [] _ _) | .w _ | .text _ | .field _ => true
  | _ => false

def TFrag.hs : List Hole → Bool
  | [] => true
  | h :: hs => TFrag.h h && TFrag.hs hs
end

end T

section C
variable (b cap : Slot → Bool) (ao : AlgId → Bool)

/-- A type a condition tests: one its environment and Parse Node do not reach. -/
def CFrag.t : TyExpr → Bool
  | .sort .. | .nt .. => true
  | .union _ _ ts => ts.all fun
    | .sort .. | .nt .. => true
    | _ => false
  | _ => false

mutual
/-- A condition hole's expressions: its binders `b` read only where a value and its `used` form mean
the same (a field's or an SDO's subject, an argument of a non-built-in algorithm) or as a predicate's
subject (`CFrag.c`, whose `is` and `is a` tests read the subject's `used` form), other variables
only where `cap`; no Parse Node, closure, phrase, hole or `?`. -/
def CFrag.e : Expr → Bool
  | .var y => cap y
  | .val _ | .math .. | .enum _ | .fieldName _ | .code .. | .term _ => true
  | .field (.var x) _ => b x || cap x
  | .field e _ => CFrag.e e
  | .sdo _ _ (.var x) [] => b x || cap x
  | .sdo _ _ e [] => CFrag.e e
  | .call (.alg a) as => ao a && CFrag.as as
  | .paren e => CFrag.e e
  | _ => false

def CFrag.as : List Expr → Bool
  | [] => true
  | .var x :: as => (b x || cap x) && CFrag.as as
  | e :: as => CFrag.e e && CFrag.as as

def CFrag.es : List Expr → Bool
  | [] => true
  | e :: es => CFrag.e e && CFrag.es es

def CFrag.p : Pred → Bool
  | .isVal _ _ vs => CFrag.es vs
  | .isTy _ _ ts => ts.all CFrag.t
  | _ => false

def CFrag.rest : List (Conj × Pred) → Bool
  | [] => true
  | (_, p) :: r => CFrag.p p && CFrag.rest r

def CFrag.c : Cond → Bool
  | .preds (.var x) p rest => (b x || cap x) && CFrag.p p && CFrag.rest rest
  | .preds e p rest => CFrag.e e && CFrag.p p && CFrag.rest rest
  | .rel _ l r => CFrag.e l && CFrag.e r
  | .and _ cs => CFrag.cs cs
  | .or _ cs => CFrag.cs cs
  | .paren c => CFrag.c c
  | .expr e => CFrag.e e
  | _ => false

def CFrag.cs : List Cond → Bool
  | [] => true
  | c :: cs => CFrag.c c && CFrag.cs cs
end

end C

mutual
/-- The variables an expression of `CFrag` reads, in order. -/
def vars.e : Expr → List Slot
  | .var y => [y]
  | .field e _ => vars.e e
  | .sdo _ _ e as => vars.e e ++ vars.es as
  | .call _ as => vars.es as
  | .paren e => vars.e e
  | _ => []

def vars.es : List Expr → List Slot
  | [] => []
  | e :: es => vars.e e ++ vars.es es

def vars.p : Pred → List Slot
  | .isVal _ _ vs => vars.es vs
  | _ => []

def vars.rest : List (Conj × Pred) → List Slot
  | [] => []
  | (_, p) :: r => vars.p p ++ vars.rest r

def vars.c : Cond → List Slot
  | .preds e p rest => vars.e e ++ vars.p p ++ vars.rest rest
  | .rel _ l r => vars.e l ++ vars.e r
  | .and _ cs => vars.cs cs
  | .or _ cs => vars.cs cs
  | .paren c => vars.c c
  | .expr e => vars.e e
  | _ => []

def vars.cs : List Cond → List Slot
  | [] => []
  | c :: cs => vars.c c ++ vars.cs cs
end

/-- The variables other than its binders `xs` a condition reads: a closure's captures. -/
def caps (xs : List Slot) (c : Cond) : List Slot := ((vars.c c).filter (!xs.contains ·)).eraseDups

/-- The Abstract Closure a condition over the binders `xs` becomes. -/
def condClo (xs : List Slot) (c : Cond) : CloLit :=
  { kind := .abstract, atomic := false, params := some xs, caps := caps xs c,
    body := [.mk [] (.ret (some (.ofCond c)))] }

/-- The capture-free algorithm a condition over the binders `0 … k-1` becomes. -/
def condAlg (id : AlgId) (xs : List Slot) (c : Cond) : Alg :=
  { id, name := "spec-cond", attrs := [], indent := 0, closures := #[],
    header := { kind := .ao, params := xs.map (fun x => ⟨x, none, false, false⟩), ret := none, recv := none, desc := [] },
    vars := (xs.map fun _ => "x").toArray, body := [.mk [] (.ret (some (.ofCond c)))] }

/-- The algorithm a type phrase means: whether its one argument is of type `t`. -/
def tyAlg (id : AlgId) (t : TyExpr) : Alg :=
  { id, name := "spec-type", attrs := [], indent := 0, closures := #[],
    header := { kind := .ao, params := [⟨0, none, false, false⟩], ret := none, recv := none, desc := [] },
    vars := #["v"], body := [.mk [] (.ret (some (.ofCond (.preds (.var 0) (.isTy false .or [t]) []))))] }

/-- A copy of the phrase algorithm `g` whose type variables `ts` are tests of type phrases. -/
def copyAlg (id : AlgId) (ts : Slot → Option PhraseId) (g : Alg) : Alg :=
  let σ : Sites := { tv := fun _ x => (ts x).map fun p => .phrase p [] }
  { g with id, body := Node.rwL σ g.body }

/-- The tables the rewrite reads: per caller, a condition's closure index; a capture-free
condition's algorithm clause; a phrase's copy for its types; NewRecord's phrase of a sort and its
modifiers. -/
structure Tables where
  clo : AlgId → List Slot → Cond → Option Nat := fun _ _ _ => none
  condAlg : List Slot → Cond → Option ClauseId := fun _ _ => none
  copy : PhraseId → List (Nat × TyExpr) → Option PhraseId := fun _ _ => none
  newRec : SortId → List SortId → Option PhraseId := fun _ _ => none

/-- Whether `P` calls `a` as an algorithm whose arguments are taken in their `used` form. -/
def aoOf (P : Prog) (a : AlgId) : Bool :=
  match P.alg a with
  | some g => g.header.kind != .builtin
  | none => false

/-- The type holes of a site, by position. -/
def typeHoles (hs : List Hole) : List (Nat × TyExpr) :=
  (hs.zipIdx.filterMap fun
    | (.t (.sort _ [] _ _), _) => none
    | (.t t, i) => some (i, t)
    | _ => none)

/-- A site's hole as rewritten in the steps of `caller` (`early`: an early-error rule's). -/
def Tables.hole (T : Tables) (P : Prog) (caller : AlgId) (early : Bool) : Hole → Option Hole
  | .bc xs c =>
    if early then
      if CFrag.c (xs.contains ·) (fun _ => false) (aoOf P) c && xs == List.range xs.length then
        (T.condAlg xs c).map fun cl => .e (.definition ⟨"", .plain, some cl⟩ false)
      else none
    else if CFrag.c (xs.contains ·) (!xs.contains ·) (aoOf P) c then
      (T.clo caller xs c).map fun k => .e (.closure k)
    else none
  | .t (.sort a [] s w) => some (.t (.sort a [] s w))
  | .t t => if TFrag.t t then some (.w 0) else none
  | h => some h

/-- A site's rewrite in the steps of `caller`: its phrase and holes. -/
def Tables.site (T : Tables) (P : Prog) (caller : AlgId) (early : Bool) (p : PhraseId) (hs : List Hole) :
    Option (PhraseId × List Hole) :=
  if !hs.any Hole.code then none else
  match P.phrase p with
  | .prim q [.hole 0] false =>
    if q == Known.pNewRecord then match hs with
      | [.t (.sort _ (m :: ms) s _)] => (T.newRec s (m :: ms)).map (·, [])
      | _ => none
    else none
  | .alg a => match P.alg a with
    | some g =>
      if g.header.kind == .builtin || g.header.recv.isSome || !g.closures.isEmpty ||
          !GFrag.ns (useOf hs) g.body then none
      else do
        let hs' ← hs.mapM (T.hole P caller early)
        let tys := typeHoles hs
        let p' ← if tys.isEmpty then some p else T.copy p tys
        some (p', hs')
    | none => none
  | _ => none

/-- The rewrite of the sites in the steps of `caller`. -/
def Tables.sites (T : Tables) (P : Prog) (caller : AlgId) (early : Bool) : Sites :=
  let f := T.site P caller early
  { e := fun p hs => (f p hs).map fun (p', hs') => .phrase p' hs'
    c := fun p hs => (f p hs).map fun (p', hs') => .phrase p' hs'
    p := fun p hs => (f p hs).map fun (p', hs') => .phrase p' hs'
    t := fun p hs => (f p hs).map fun (p', hs') => .phrase p' hs'
    s := fun p hs => (f p hs).map fun (p', hs') => .phrase p' hs'
    m := fun p hs => (f p hs).map fun (p', hs') => .mutate p' hs' }

/-- What the rewrite refers to: closures appended per caller (and the closure-less SDO rows that
get some), algorithms and phrases. -/
structure Decl where
  clos : AlgId → List CloLit := fun _ => []
  rows : List SdoRow := []
  algs : List Alg := []
  phrases : List (PhraseId × PhraseMeaning) := []

/-- A caller's closures with its declared ones after them. -/
def Decl.extend (d : Decl) (a : AlgId) (cs : Array CloLit) : Array CloLit := cs ++ (d.clos a).toArray

/-- An SDO row with its declared closures. -/
def Decl.row (d : Decl) (r : SdoRow) : SdoRow := { r with closures := d.extend r.id r.closures }

/-- `P` with `d`'s declarations (found by `Src.algKey`): its algorithms and phrases, and the callers' closures. -/
def Decl.declare (d : Decl) (P : Prog) : Prog :=
  { P with
    alg := fun a => match d.algs.find? (Src.algKey ·.id == Src.algKey a) with
      | some g => some g
      | none => (P.alg a).map fun g => { g with closures := d.extend g.id g.closures }
    row := fun s p => (P.row s p).map d.row
    rowOf := fun a => match P.rowOf a with
      | some r => some (d.row r)
      | none => (d.rows.find? (Src.algKey ·.id == Src.algKey a)).map d.row
    phrase := fun p => (d.phrases.lookup p).getD (P.phrase p) }

/-- The caller of a table's sites: an early-error rule's (no closures), so its id is not read. -/
def tableCaller : AlgId := ⟨0, 0⟩

/-- The declared program `P` with the sites of its algorithms, SDO rows, early-error rules and tables rewritten. -/
def Tables.rewrite (T : Tables) (P : Prog) : Prog :=
  { P with
    alg := fun a => (P.alg a).map fun g => Alg.rw (T.sites P g.id false) g
    row := fun s p => (P.row s p).map fun r => SdoRow.rw (T.sites P r.id false) r
    rowOf := fun a => (P.rowOf a).map fun r => SdoRow.rw (T.sites P r.id false) r
    early := fun p => (P.early p).map fun r => EarlyRow.rw (T.sites P r.id true) r
    table := fun t => (P.table t).map (Table.rw (T.sites P tableCaller true))
    clauseTables := fun c => (P.clauseTables c).map (Table.rw (T.sites P tableCaller true)) }

end Ecma.Spec
