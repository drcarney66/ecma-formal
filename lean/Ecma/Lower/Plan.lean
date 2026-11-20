module

public import Ecma.Lower.Specialize
public import Ecma.Lower.Src

@[expose] public section

/-!
# The specialization's plan for a source

`scan.e` … `scan.table`: the phrase sites with a code hole, at the positions `Sites` rewrites.
`Plan.ofSrc`: the tables and declarations of the rewrite, from the sites of the algorithms, SDO rows,
their closures, the early-error rules and the tables (as early-error rules): a closure per caller and
condition, a clause per early-error condition, type, and copy of a phrase algorithm, and a phrase per type, copy, and
NewRecord of a sort and its modifiers. `Plan.left`: the sites with a code hole the rewrite leaves.
-/

namespace Ecma.Spec

mutual
/-- Structural equality of expressions. -/
def eqE : Expr → Expr → Bool
  | .var x, y => match y with | .var x' => x == x' | _ => false
  | .val v, y => match y with | .val v' => v == v' | _ => false
  | .math s m, y => match y with | .math s' m' => s == s' && m == m' | _ => false
  | .enum e, y => match y with | .enum e' => e == e' | _ => false
  | .param p, y => match y with | .param p' => p == p' | _ => false
  | .intrinsic i, y => match y with | .intrinsic i' => i == i' | _ => false
  | .fieldName f, y => match y with | .fieldName f' => f == f' | _ => false
  | .nt n as, y => match y with | .nt n' as' => n == n' && as == as' | _ => false
  | .prod ps r, y => match y with | .prod ps' r' => ps == ps' && r == r' | _ => false
  | .codeUnit n d k, y => match y with | .codeUnit n' d' k' => n == n' && d == d' && k == k' | _ => false
  | .codePoint n d k, y => match y with | .codePoint n' d' k' => n == n' && d == d' && k == k' | _ => false
  | .code s w, y => match y with | .code s' w' => s == s' && w == w' | _ => false
  | .term s, y => match y with | .term s' => s == s' | _ => false
  | .call f as, y => match y with | .call f' as' => f == f' && eqEs as as' | _ => false
  | .callAt g as, y => match y with | .callAt g' as' => g == g' && eqEs as as' | _ => false
  | .sdo s a e as, y => match y with | .sdo s' a' e' as' => s == s' && a == a' && eqE e e' && eqEs as as' | _ => false
  | .component c a e, y => match y with | .component c' a' e' => c == c' && a == a' && eqE e e' | _ => false
  | .field e f, y => match y with | .field e' f' => eqE e e' && f == f' | _ => false
  | .imethod e m as, y => match y with | .imethod e' m' as' => eqE e e' && m == m' && eqEs as as' | _ => false
  | .cmethod e m as, y => match y with | .cmethod e' m' as' => eqE e e' && m == m' && eqEs as as' | _ => false
  | .apply f as, y => match y with | .apply f' as' => eqE f f' && eqEs as as' | _ => false
  | .index e i, y => match y with | .index e' i' => eqE e e' && eqE i i' | _ => false
  | .q e, y => match y with | .q e' => eqE e e' | _ => false
  | .bang e, y => match y with | .bang e' => eqE e e' | _ => false
  | .bangAt r e, y => match y with | .bangAt r' e' => r == r' && eqE e e' | _ => false
  | .erratum r k e, y => match y with | .erratum r' k' e' => r == r' && k == k' && eqE e e' | _ => false
  | .un o e, y => match y with | .un o' e' => o == o' && eqE e e' | _ => false
  | .bin o a b, y => match y with | .bin o' a' b' => o == o' && eqE a a' && eqE b b' | _ => false
  | .paren e, y => match y with | .paren e' => eqE e e' | _ => false
  | .list es, y => match y with | .list es' => eqEs es es' | _ => false
  | .record a k fs, y => match y with | .record a' k' fs' => a == a' && k == k' && eqFs fs fs' | _ => false
  | .resumedWith e, y => match y with | .resumedWith e' => eqE e e' | _ => false
  | .thisNode, y => match y with | .thisNode => true | _ => false
  | .child k n s, y => match y with | .child k' n' s' => k == k' && n == n' && s == s' | _ => false
  | .childOf e n s, y => match y with | .childOf e' n' s' => eqE e e' && n == n' && s == s' | _ => false
  | .thisValue b, y => match y with | .thisValue b' => b == b' | _ => false
  | .newTarget, y => match y with | .newTarget => true | _ => false
  | .annot as e, y => match y with | .annot as' e' => as == as' && eqE e e' | _ => false
  | .xref x, y => match y with | .xref x' => x == x' | _ => false
  | .closure k, y => match y with | .closure k' => k == k' | _ => false
  | .table t x, y => match y with | .table t' x' => t == t' && x == x' | _ => false
  | .definition x a, y => match y with | .definition x' a' => x == x' && a == a' | _ => false
  | .tableStep t k x, y => match y with | .tableStep t' k' x' => t == t' && eqE k k' && x == x' | _ => false
  | .extreme m x t c, y => match y with | .extreme m' x' t' c' => m == m' && x == x' && eqT t t' && eqC c c' | _ => false
  | .phrase p hs, y => match y with | .phrase p' hs' => p == p' && eqHs hs hs' | _ => false
  | .prose ch ps, y => match y with | .prose ch' ps' => ch == ch' && eqPs ps ps' | _ => false
  | .bnd x, y => match y with | .bnd x' => x == x' | _ => false
  | .data d, y => match y with | .data d' => d == d' | _ => false
  | .ofCond c, y => match y with | .ofCond c' => eqC c c' | _ => false

def eqEs : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => eqE a b && eqEs as bs
  | _, _ => false

def eqFs : List (FieldId × Expr) → List (FieldId × Expr) → Bool
  | [], [] => true
  | (k, a) :: as, (k', b) :: bs => k == k' && eqE a b && eqFs as bs
  | _, _ => false

def eqP : Pred → Pred → Bool
  | .isVal n f vs, y => match y with | .isVal n' f' vs' => n == n' && f == f' && eqEs vs vs' | _ => false
  | .isTy n f ts, y => match y with | .isTy n' f' ts' => n == n' && f == f' && eqTs ts ts' | _ => false
  | .phrase p hs, y => match y with | .phrase p' hs' => p == p' && eqHs hs hs' | _ => false
  | .call f as n, y => match y with | .call f' as' n' => f == f' && eqEs as as' && n == n' | _ => false

def eqRs : List (Conj × Pred) → List (Conj × Pred) → Bool
  | [], [] => true
  | (k, a) :: as, (k', b) :: bs => k == k' && eqP a b && eqRs as bs
  | _, _ => false

def eqC : Cond → Cond → Bool
  | .preds e p r, y => match y with | .preds e' p' r' => eqE e e' && eqP p p' && eqRs r r' | _ => false
  | .rel o a b, y => match y with | .rel o' a' b' => o == o' && eqE a a' && eqE b b' | _ => false
  | .and f cs, y => match y with | .and f' cs' => f == f' && eqCs cs cs' | _ => false
  | .or f cs, y => match y with | .or f' cs' => f == f' && eqCs cs cs' | _ => false
  | .paren c, y => match y with | .paren c' => eqC c c' | _ => false
  | .alg a, y => match y with | .alg a' => a == a' | _ => false
  | .phrase p hs, y => match y with | .phrase p' hs' => p == p' && eqHs hs hs' | _ => false
  | .prose ch ps, y => match y with | .prose ch' ps' => ch == ch' && eqPs ps ps' | _ => false
  | .expr e, y => match y with | .expr e' => eqE e e' | _ => false
  | .pass k, y => match y with | .pass k' => k == k' | _ => false

def eqCs : List Cond → List Cond → Bool
  | [], [] => true
  | a :: as, b :: bs => eqC a b && eqCs as bs
  | _, _ => false

def eqT : TyExpr → TyExpr → Bool
  | .sort a ms s w, y => match y with | .sort a' ms' s' w' => a == a' && ms == ms' && s == s' && w == w' | _ => false
  | .listOf a t, y => match y with | .listOf a' t' => a == a' && eqT t t' | _ => false
  | .union f c ts, y => match y with | .union f' c' ts' => f == f' && c == c' && eqTs ts ts' | _ => false
  | .completion t, y => match y with | .completion t' => eqTo t t' | _ => false
  | .interval t lo hi, y => match y with | .interval t' lo' hi' => eqT t t' && eqE lo lo' && eqE hi hi' | _ => false
  | .value v, y => match y with | .value v' => eqE v v' | _ => false
  | .var a x, y => match y with | .var a' x' => a == a' && x == x' | _ => false
  | .nt a n s, y => match y with | .nt a' n' s' => a == a' && n == n' && s == s' | _ => false
  | .record fs, y => match y with | .record fs' => eqTfs fs fs' | _ => false
  | .that t p r, y => match y with | .that t' p' r' => eqT t t' && eqP p p' && eqRs r r' | _ => false
  | .phrase p hs, y => match y with | .phrase p' hs' => p == p' && eqHs hs hs' | _ => false
  | .prose ps, y => match y with | .prose ps' => eqPs ps ps' | _ => false
  | .pred p, y => match y with | .pred p' => eqP p p' | _ => false

def eqTs : List TyExpr → List TyExpr → Bool
  | [], [] => true
  | a :: as, b :: bs => eqT a b && eqTs as bs
  | _, _ => false

def eqTo : Option TyExpr → Option TyExpr → Bool
  | none, none => true
  | some a, some b => eqT a b
  | _, _ => false

def eqTfs : List (FieldId × TyExpr) → List (FieldId × TyExpr) → Bool
  | [], [] => true
  | (k, a) :: as, (k', b) :: bs => k == k' && eqT a b && eqTfs as bs
  | _, _ => false

def eqH : Hole → Hole → Bool
  | .e x, y => match y with | .e x' => eqE x x' | _ => false
  | .c x, y => match y with | .c x' => eqC x x' | _ => false
  | .t x, y => match y with | .t x' => eqT x x' | _ => false
  | .b x, y => match y with | .b x' => x == x' | _ => false
  | .bc xs x, y => match y with | .bc xs' x' => xs == xs' && eqC x x' | _ => false
  | .w i, y => match y with | .w i' => i == i' | _ => false
  | .l f xs, y => match y with | .l f' xs' => f == f' && eqEs xs xs' | _ => false
  | .text s, y => match y with | .text s' => s == s' | _ => false
  | .field f, y => match y with | .field f' => f == f' | _ => false

def eqHs : List Hole → List Hole → Bool
  | [], [] => true
  | a :: as, b :: bs => eqH a b && eqHs as bs
  | _, _ => false

def eqPart : Part → Part → Bool
  | .text s, y => match y with | .text s' => s == s' | _ => false
  | .hole h, y => match y with | .hole h' => eqH h h' | _ => false

def eqPs : List Part → List Part → Bool
  | [], [] => true
  | a :: as, b :: bs => eqPart a b && eqPs as bs
  | _, _ => false
end

instance : BEq Cond := ⟨eqC⟩
instance : BEq TyExpr := ⟨eqT⟩

/-- A phrase site, kept if one of its holes is code. -/
def site1 (p : PhraseId) (hs : List Hole) : List (PhraseId × List Hole) :=
  if hs.any Hole.code then [(p, hs)] else []

abbrev Found := List (PhraseId × List Hole)

mutual
/-- The sites of `e` with a code hole. -/
def scan.e : Expr → Found
  | .call _ as | .callAt _ as => scan.es as
  | .sdo _ _ e as => scan.e e ++ scan.es as
  | .component _ _ e => scan.e e
  | .field e _ => scan.e e
  | .imethod e _ as => scan.e e ++ scan.es as
  | .cmethod e _ as => scan.e e ++ scan.es as
  | .apply f as => scan.e f ++ scan.es as
  | .index e i => scan.e e ++ scan.e i
  | .q e => scan.e e
  | .bang e => scan.e e
  | .bangAt _ e => scan.e e
  | .erratum _ _ e => scan.e e
  | .un _ e => scan.e e
  | .bin _ a b => scan.e a ++ scan.e b
  | .paren e => scan.e e
  | .list es => scan.es es
  | .record _ _ fs => scan.fs fs
  | .resumedWith e => scan.e e
  | .childOf e _ _ => scan.e e
  | .annot _ e => scan.e e
  | .tableStep _ k _ => scan.e k
  | .extreme _ _ ty c => scan.t ty ++ scan.c c
  | .phrase p hs => scan.hs hs ++ site1 p hs
  | .prose _ ps => scan.ps ps
  | .ofCond c => scan.c c
  | _ => []

def scan.es : List Expr → Found
  | [] => []
  | e :: es => scan.e e ++ scan.es es

def scan.f : FieldId × Expr → Found
  | (_, e) => scan.e e

def scan.fs : List (FieldId × Expr) → Found
  | [] => []
  | fe :: fs => scan.f fe ++ scan.fs fs

def scan.p : Pred → Found
  | .isVal _ _ vs => scan.es vs
  | .isTy _ _ ts => scan.ts ts
  | .phrase p hs => scan.hs hs ++ site1 p hs
  | .call _ as _ => scan.es as

def scan.r : Conj × Pred → Found
  | (_, p) => scan.p p

def scan.rs : List (Conj × Pred) → Found
  | [] => []
  | r :: rs => scan.r r ++ scan.rs rs

def scan.c : Cond → Found
  | .preds e p rest => scan.e e ++ scan.p p ++ scan.rs rest
  | .rel _ a b => scan.e a ++ scan.e b
  | .and _ cs => scan.cs cs
  | .or _ cs => scan.cs cs
  | .paren c => scan.c c
  | .alg _ => []
  | .phrase p hs => scan.hs hs ++ site1 p hs
  | .prose _ ps => scan.ps ps
  | .expr e => scan.e e
  | .pass _ => []

def scan.cs : List Cond → Found
  | [] => []
  | c :: cs => scan.c c ++ scan.cs cs

def scan.co : Option Cond → Found
  | none => []
  | some c => scan.c c

def scan.t : TyExpr → Found
  | .listOf _ t => scan.t t
  | .union _ _ ts => scan.ts ts
  | .interval t lo hi => scan.t t ++ scan.e lo ++ scan.e hi
  | .value v => scan.e v
  | .that t p rest => scan.t t ++ scan.p p ++ scan.rs rest
  | .phrase p hs => scan.hs hs ++ site1 p hs
  | .completion t => scan.to t
  | .record fs => scan.tfs fs
  | .prose ps => scan.ps ps
  | .pred p => scan.p p
  | _ => []

def scan.ts : List TyExpr → Found
  | [] => []
  | t :: ts => scan.t t ++ scan.ts ts

def scan.to : Option TyExpr → Found
  | none => []
  | some t => scan.t t

def scan.tf : FieldId × TyExpr → Found
  | (_, t) => scan.t t

def scan.tfs : List (FieldId × TyExpr) → Found
  | [] => []
  | ft :: fs => scan.tf ft ++ scan.tfs fs

def scan.h : Hole → Found
  | .e x => scan.e x
  | .c x => scan.c x
  | .l _ xs => scan.es xs
  | _ => []

def scan.hs : List Hole → Found
  | [] => []
  | h :: hs => scan.h h ++ scan.hs hs

def scan.part : Part → Found
  | .text _ => []
  | .hole h => scan.h h

def scan.ps : List Part → Found
  | [] => []
  | p :: ps => scan.part p ++ scan.ps ps
end

mutual
/-- The sites of a place with a code hole. -/
def scan.place : Place → Found
  | .var _ => []
  | .field e _ => scan.e e
  | .expr e => scan.e e

def scan.b : Body → Found
  | .inline s => scan.s s
  | .block ns => scan.ns ns

def scan.s : Stmt → Found
  | .let_ _ e => scan.e e
  | .letMany _ e _ => scan.e e
  | .set p e => scan.place p ++ scan.e e
  | .ret e => scan.ret e
  | .perform e => scan.e e
  | .if_ c b arms els => scan.c c ++ scan.b b ++ scan.arms arms ++ scan.armO els
  | .ifElse c s1 s2 => scan.c c ++ scan.s s1 ++ scan.s s2
  | .assert c => scan.c c
  | .assertAt _ c => scan.c c
  | .assertIf c d => scan.c c ++ scan.c d
  | .throwVal e => scan.e e
  | .repeat_ b => scan.ns b
  | .repeatWhile c b => scan.c c ++ scan.ns b
  | .repeatUntil c b => scan.c c ++ scan.ns b
  | .forEach _ ty l _ b => scan.to ty ++ scan.e l ++ scan.b b
  | .forEachRec _ _ l b => scan.e l ++ scan.b b
  | .forRange _ lo _ hi _ _ b => scan.e lo ++ scan.e hi ++ scan.b b
  | .mutate p hs => scan.hs hs ++ site1 p hs
  | .forSuchThat _ ty c _ b => scan.t ty ++ scan.c c ++ scan.b b
  | .forKeys _ o c _ b => scan.e o ++ scan.c c ++ scan.b b
  | .forIndex _ l b => scan.e l ++ scan.b b
  | .forChildren _ b => scan.b b
  | .forChildrenOf _ e b => scan.e e ++ scan.b b
  | .repeatN e b => scan.e e ++ scan.ns b
  | .retSee e _ => scan.e e
  | .suspend c _ => scan.e c
  | .push c _ => scan.e c
  | .remove c _ => scan.e c
  | .removeRestore c r => scan.e c ++ scan.e r
  | .resumeLet c v _ _ => scan.e c ++ scan.e v
  | .resume c v => scan.e c ++ scan.e v
  | .setCodeState c f => scan.e c ++ scan.e f
  | .readings _ lit alts => scan.s lit ++ scan.alts alts
  | .findSuchThat _ ty c _ f => scan.t ty ++ scan.c c ++ scan.s f
  | .letSuchThat _ c objs => scan.c c ++ scan.objs objs
  | .macro _ as => scan.es as
  | .phrase p hs => scan.hs hs ++ site1 p hs
  | .prose _ ps => scan.ps ps
  | .expanded _ as ns => scan.es as ++ scan.ns ns
  | _ => []

def scan.ret : Option Expr → Found
  | none => []
  | some e => scan.e e

def scan.alt : Reading × List Node → Found
  | (_, ns) => scan.ns ns

def scan.alts : List (Reading × List Node) → Found
  | [] => []
  | a :: as => scan.alt a ++ scan.alts as

def scan.obj : Bool × Expr → Found
  | (_, e) => scan.e e

def scan.objs : List (Bool × Expr) → Found
  | [] => []
  | o :: os => scan.obj o ++ scan.objs os

def scan.n : Node → Found
  | .mk _ s => scan.s s

def scan.ns : List Node → Found
  | [] => []
  | n :: ns => scan.n n ++ scan.ns ns

def scan.arm : Arm → Found
  | .mk _ c b => scan.co c ++ scan.b b

def scan.arms : List Arm → Found
  | [] => []
  | a :: as => scan.arm a ++ scan.arms as

def scan.armO : Option Arm → Found
  | none => []
  | some a => scan.arm a
end

mutual
/-- The sites of an early-error sentence with a code hole. -/
def scan.es1 : EarlySentence → Found
  | .syntaxError _ c u => scan.c c ++ scan.u u
  | .syntaxErrorIns c d => scan.c c ++ scan.c d
  | .mustCover p t => scan.e p ++ scan.t t
  | .ifInline c s => scan.c c ++ scan.es1 s
  | .forEachIn _ t l c _ => scan.t t ++ scan.e l ++ scan.c c
  | .notApplied c _ => scan.c c
  | .layout _ ss => scan.esList ss
  | .readings _ lit alts => scan.esList lit ++ scan.esAlts alts
  | _ => []

def scan.u : Option (UnlessForm × Cond) → Found
  | none => []
  | some (_, d) => scan.c d

def scan.esList : List EarlySentence → Found
  | [] => []
  | s :: ss => scan.es1 s ++ scan.esList ss

def scan.esAlts : List (Reading × List EarlySentence) → Found
  | [] => []
  | (_, ss) :: rest => scan.esList ss ++ scan.esAlts rest
end

/-- The sites of a table cell's type with a code hole. -/
def scan.tty : TTy → Found
  | .ty t => scan.t t
  | .records fs => scan.tfs fs

mutual
/-- The sites of a table cell with a code hole, at the positions `CellBody.rw` rewrites. -/
def scan.cell : CellBody → Found
  | .stmt s => scan.s s
  | .expr e => scan.e e
  | .ty t => scan.tty t
  | .sig g => (g.params.map (·.ty) ++ [g.ret]).flatMap scan.tty
  | .lines cs => scan.cells cs
  | .dfn c => scan.cell c
  | .code c => scan.cell c
  | .link _ c => scan.cell c
  | _ => []

def scan.cells : List CellBody → Found
  | [] => []
  | c :: cs => scan.cell c ++ scan.cells cs
end

/-- The sites of a table's cells with a code hole. -/
def scan.table (t : Table) : Found := t.rows.flatMap (·.cells.flatMap (scan.cell ·.body))

/-- The sites of an algorithm's or SDO row's steps and closures with a code hole. -/
def scan.body (body : List Node) (cs : Array CloLit) : Found :=
  scan.ns body ++ cs.toList.flatMap (scan.ns ·.body)

/-- Tables that give every request an entry: a site they rewrite is one whose premises hold. -/
def Tables.probe : Tables :=
  { clo := fun _ _ _ => some 0, condAlg := fun _ _ => some 0, copy := fun _ _ => some 0,
    newRec := fun _ _ => some 0 }

/-- The sites of a source, by caller (`true`: an early-error rule's, or a table's as one); the source
macro-expanded. -/
def callers (s : Src) : List (AlgId × Bool × Found) :=
  s.algs.map (fun g => (g.id, false, scan.body g.body g.closures)) ++
  s.rows.map (fun r => (r.id, false, scan.body r.body r.closures)) ++
  s.earlyRows.map (fun r => (r.id, true, scan.esList r.body)) ++
  s.tables.map (fun t => (tableCaller, true, scan.table t))

/-- `xs` without repeats, in order of first occurrence. -/
def nub {α} [BEq α] (xs : List α) : List α := xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The specialization's tables and declarations, and the numbering they were built from. -/
structure Plan where
  /-- per caller, its closures' count and the conditions its declared closures are -/
  clos : List (AlgId × Nat × List (List Slot × Cond))
  /-- the early-error conditions, from clause `c0` -/
  conds : List (List Slot × Cond)
  /-- the types, from clause `c0 + conds.length` and phrase `p0` -/
  types : List TyExpr
  /-- the copies of a phrase's algorithm for its types, after the types' clauses and phrases -/
  copies : List (PhraseId × List (Nat × TyExpr))
  /-- NewRecord's sorts and modifiers, after the copies' phrases -/
  newRecs : List (SortId × List SortId)
  c0 : ClauseId
  p0 : PhraseId

namespace Plan
variable (pl : Plan)

def cT : ClauseId := pl.c0 + pl.conds.length
def cC : ClauseId := pl.cT + pl.types.length
def pC : PhraseId := pl.p0 + pl.types.length
def pN : PhraseId := pl.pC + pl.copies.length

/-- The tables the rewrite reads. -/
def tables : Tables where
  clo a xs c := (pl.clos.lookup a).bind fun (n, cs) => (cs.idxOf? (xs, c)).map (n + ·)
  condAlg xs c := (pl.conds.idxOf? (xs, c)).map (pl.c0 + ·)
  copy p tys := (pl.copies.idxOf? (p, tys)).map (pl.pC + ·)
  newRec s ms := (pl.newRecs.idxOf? (s, ms)).map (pl.pN + ·)

/-- A type's phrase. -/
def tyPhrase (t : TyExpr) : Option PhraseId := (pl.types.idxOf? t).map (pl.p0 + ·)

/-- The declarations the rewrite refers to, the phrase algorithms read in `P`; `rows`, the
closure-less SDO rows of the source. -/
def decl (P : Prog) (rows : List SdoRow) : Decl where
  clos a := ((pl.clos.lookup a).map fun (_, cs) => cs.map fun (xs, c) => condClo xs c).getD []
  rows := rows.filter fun r => r.closures.isEmpty && (pl.clos.lookup r.id).isSome
  algs :=
    pl.conds.zipIdx.map (fun ((xs, c), i) => condAlg ⟨pl.c0 + i, 0⟩ xs c) ++
    pl.types.zipIdx.map (fun (t, i) => tyAlg ⟨pl.cT + i, 0⟩ t) ++
    pl.copies.zipIdx.filterMap fun ((p, tys), i) => match P.phrase p with
      | .alg a => (P.alg a).map fun g =>
          copyAlg ⟨pl.cC + i, 0⟩ (fun y => (tys.lookup y).bind pl.tyPhrase) g
      | _ => none
  phrases :=
    pl.types.zipIdx.map (fun (_, i) => (pl.p0 + i, .alg ⟨pl.cT + i, 0⟩)) ++
    pl.copies.zipIdx.map (fun (_, i) => (pl.pC + i, .alg ⟨pl.cC + i, 0⟩)) ++
    pl.newRecs.zipIdx.map fun ((s, ms), i) =>
      (pl.pN + i, .prim Known.pNewRecord (.sort s :: ms.map .sort) false)

end Plan

/-- The plan for a source's sites whose premises hold, the source macro-expanded. -/
def Plan.ofSrc (s : Src) : Plan :=
  let s' := s.expandMacros
  let P := s.prog
  let live := (callers s').map fun (a, early, fs) =>
    (a, early, fs.filter fun (p, hs) => (Tables.probe.site P a early p hs).isSome)
  let isAlg := fun p => match P.phrase p with | .alg _ => true | _ => false
  let bcs := fun (fs : Found) => fs.flatMap fun (p, hs) =>
    if isAlg p then hs.filterMap fun | .bc xs c => some (xs, c) | _ => none else []
  let cloCount := fun a => ((s'.algMap[Src.algKey a]?).map (·.closures.size)).getD
    (((s'.rows.find? (·.id == a)).map (·.closures.size)).getD 0)
  let clos := live.filterMap fun (a, early, fs) =>
    let cs := nub (bcs fs)
    if early || cs.isEmpty then none else some (a, cloCount a, cs)
  let conds := nub (live.flatMap fun (_, early, fs) => if early then bcs fs else [])
  let algSites := live.flatMap fun (_, _, fs) => fs.filter (isAlg ·.1)
  let copies := nub (algSites.filterMap fun (p, hs) =>
    let tys := typeHoles hs
    if tys.isEmpty then none else some (p, tys))
  let types := nub (copies.flatMap fun (_, tys) => tys.map (·.2))
  let newRecs := nub (live.flatMap fun (_, _, fs) => fs.filterMap fun (p, hs) =>
    if isAlg p then none else match hs with
      | [.t (.sort _ (m :: ms) k _)] => some (k, m :: ms)
      | _ => none)
  { clos, conds, types, copies, newRecs, c0 := s.decls.clauses.size, p0 := s.decls.phrases.size }

end Ecma.Spec
