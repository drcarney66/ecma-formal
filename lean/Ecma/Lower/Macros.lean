module

public import Ecma.Notation.Syntax

@[expose] public section

/-!
# Macro expansion

A macro use `IfAbruptRejectPromise(_v_, _c_).` "means the same thing as" its expansion's steps with the
parameters replaced by the use's variables (§27.5.1.1.1, §7.4.13).
-/

namespace Ecma

section Rename
variable (σ : Slot → Slot)

mutual
/-- `e` with each variable `x` written `σ x`. -/
def Expr.rename : Expr → Expr
  | .var x => .var (σ x)
  | .call f as => .call f (Expr.renameL as)
  | .callAt a as => .callAt a (Expr.renameL as)
  | .sdo s a e as => .sdo s a (Expr.rename e) (Expr.renameL as)
  | .component c a e => .component c a (Expr.rename e)
  | .field e f => .field (Expr.rename e) f
  | .imethod e m as => .imethod (Expr.rename e) m (Expr.renameL as)
  | .cmethod e m as => .cmethod (Expr.rename e) m (Expr.renameL as)
  | .apply f as => .apply (Expr.rename f) (Expr.renameL as)
  | .index e i => .index (Expr.rename e) (Expr.rename i)
  | .q e => .q (Expr.rename e)
  | .bang e => .bang (Expr.rename e)
  | .bangAt r e => .bangAt r (Expr.rename e)
  | .erratum r s e => .erratum r s (Expr.rename e)
  | .un o e => .un o (Expr.rename e)
  | .bin o a b => .bin o (Expr.rename a) (Expr.rename b)
  | .paren e => .paren (Expr.rename e)
  | .list es => .list (Expr.renameL es)
  | .record a k fs => .record a k (Expr.renameFs fs)
  | .resumedWith e => .resumedWith (Expr.rename e)
  | .childOf e n s => .childOf (Expr.rename e) n s
  | .annot ats e => .annot ats (Expr.rename e)
  | .tableStep t k x => .tableStep t (Expr.rename k) x
  | .extreme mx x ty c => .extreme mx (σ x) (TyExpr.rename ty) (Cond.rename c)
  | .phrase p hs => .phrase p (Hole.renameL hs)
  | .prose ch ps => .prose ch (Part.renameL ps)
  | .bnd x => .bnd (σ x)
  | .ofCond c => .ofCond (Cond.rename c)
  | e => e

def Expr.renameL : List Expr → List Expr
  | [] => []
  | e :: es => Expr.rename e :: Expr.renameL es

def Expr.renameF : FieldId × Expr → FieldId × Expr
  | (f, e) => (f, Expr.rename e)

def Expr.renameFs : List (FieldId × Expr) → List (FieldId × Expr)
  | [] => []
  | fe :: fs => Expr.renameF fe :: Expr.renameFs fs

def Pred.rename : Pred → Pred
  | .isVal neg f vs => .isVal neg f (Expr.renameL vs)
  | .isTy neg f ts => .isTy neg f (TyExpr.renameL ts)
  | .phrase p hs => .phrase p (Hole.renameL hs)
  | .call f as neg => .call f (Expr.renameL as) neg

def Pred.renameR : Conj × Pred → Conj × Pred
  | (j, p) => (j, Pred.rename p)

def Pred.renameRs : List (Conj × Pred) → List (Conj × Pred)
  | [] => []
  | r :: rs => Pred.renameR r :: Pred.renameRs rs

def Cond.rename : Cond → Cond
  | .preds e p rest => .preds (Expr.rename e) (Pred.rename p) (Pred.renameRs rest)
  | .rel o a b => .rel o (Expr.rename a) (Expr.rename b)
  | .and f cs => .and f (Cond.renameL cs)
  | .or f cs => .or f (Cond.renameL cs)
  | .paren c => .paren (Cond.rename c)
  | .alg a => .alg a
  | .phrase p hs => .phrase p (Hole.renameL hs)
  | .prose ch ps => .prose ch (Part.renameL ps)
  | .expr e => .expr (Expr.rename e)
  | .pass k => .pass k

def Cond.renameL : List Cond → List Cond
  | [] => []
  | c :: cs => Cond.rename c :: Cond.renameL cs

def Cond.renameO : Option Cond → Option Cond
  | none => none
  | some c => some (Cond.rename c)

def TyExpr.rename : TyExpr → TyExpr
  | .listOf a t => .listOf a (TyExpr.rename t)
  | .union f c ts => .union f c (TyExpr.renameL ts)
  | .completion t => .completion (TyExpr.renameO t)
  | .interval t lo hi => .interval (TyExpr.rename t) (Expr.rename lo) (Expr.rename hi)
  | .value v => .value (Expr.rename v)
  | .var a x => .var a (σ x)
  | .record fs => .record (TyExpr.renameFs fs)
  | .that t p rest => .that (TyExpr.rename t) (Pred.rename p) (Pred.renameRs rest)
  | .phrase p hs => .phrase p (Hole.renameL hs)
  | .prose ps => .prose (Part.renameL ps)
  | .pred p => .pred (Pred.rename p)
  | t => t

def TyExpr.renameL : List TyExpr → List TyExpr
  | [] => []
  | t :: ts => TyExpr.rename t :: TyExpr.renameL ts

def TyExpr.renameO : Option TyExpr → Option TyExpr
  | none => none
  | some t => some (TyExpr.rename t)

def TyExpr.renameF : FieldId × TyExpr → FieldId × TyExpr
  | (f, t) => (f, TyExpr.rename t)

def TyExpr.renameFs : List (FieldId × TyExpr) → List (FieldId × TyExpr)
  | [] => []
  | ft :: fs => TyExpr.renameF ft :: TyExpr.renameFs fs

def Hole.rename : Hole → Hole
  | .e x => .e (Expr.rename x)
  | .c x => .c (Cond.rename x)
  | .t x => .t (TyExpr.rename x)
  | .b x => .b (σ x)
  | .bc xs x => .bc (xs.map σ) (Cond.rename x)
  | .l f xs => .l f (Expr.renameL xs)
  | h => h

def Hole.renameL : List Hole → List Hole
  | [] => []
  | h :: hs => Hole.rename h :: Hole.renameL hs

def Part.rename : Part → Part
  | .text s => .text s
  | .hole h => .hole (Hole.rename h)

def Part.renameL : List Part → List Part
  | [] => []
  | p :: ps => Part.rename p :: Part.renameL ps

def Place.rename : Place → Place
  | .var x => .var (σ x)
  | .field e f => .field (Expr.rename e) f
  | .expr e => .expr (Expr.rename e)

def Body.rename : Body → Body
  | .inline s => .inline (Stmt.rename s)
  | .block ns => .block (Node.renameL ns)

def Stmt.rename : Stmt → Stmt
  | .let_ x e => .let_ (σ x) (Expr.rename e)
  | .letMany xs e v => .letMany (xs.map σ) (Expr.rename e) v
  | .set p e => .set (Place.rename p) (Expr.rename e)
  | .ret e => .ret (Stmt.renameRet e)
  | .perform e => .perform (Expr.rename e)
  | .if_ c b arms els => .if_ (Cond.rename c) (Body.rename b) (Arm.renameL arms) (Arm.renameO els)
  | .ifElse c s1 s2 => .ifElse (Cond.rename c) (Stmt.rename s1) (Stmt.rename s2)
  | .assert c => .assert (Cond.rename c)
  | .assertAt r c => .assertAt r (Cond.rename c)
  | .assertIf c d => .assertIf (Cond.rename c) (Cond.rename d)
  | .throwVal e => .throwVal (Expr.rename e)
  | .note ps => .note (Part.renameL ps)
  | .repeat_ b => .repeat_ (Node.renameL b)
  | .repeatWhile c b => .repeatWhile (Cond.rename c) (Node.renameL b)
  | .repeatUntil c b => .repeatUntil (Cond.rename c) (Node.renameL b)
  | .forEach x ty l rev b => .forEach (σ x) (TyExpr.renameO ty) (Expr.rename l) rev (Body.rename b)
  | .forEachRec fs x l b => .forEachRec fs (σ x) (Expr.rename l) (Body.rename b)
  | .forRange x lo li hi hi' desc b =>
    .forRange (σ x) (Expr.rename lo) li (Expr.rename hi) hi' desc (Body.rename b)
  | .mutate p hs => .mutate p (Hole.renameL hs)
  | .forSuchThat x ty c o b => .forSuchThat (σ x) (TyExpr.rename ty) (Cond.rename c) o (Body.rename b)
  | .forKeys x o c order b => .forKeys (σ x) (Expr.rename o) (Cond.rename c) order (Body.rename b)
  | .forIndex x l b => .forIndex (σ x) (Expr.rename l) (Body.rename b)
  | .forChildren x b => .forChildren (σ x) (Body.rename b)
  | .forChildrenOf x e b => .forChildrenOf (σ x) (Expr.rename e) (Body.rename b)
  | .repeatN e b => .repeatN (Expr.rename e) (Node.renameL b)
  | .retSee e x => .retSee (Expr.rename e) x
  | .suspend c v => .suspend (Expr.rename c) v
  | .push c v => .push (Expr.rename c) v
  | .remove c v => .remove (Expr.rename c) v
  | .removeRestore c r => .removeRestore (Expr.rename c) (Expr.rename r)
  | .resumeLet c v x ats => .resumeLet (Expr.rename c) (Expr.rename v) (σ x) ats
  | .resume c v => .resume (Expr.rename c) (Expr.rename v)
  | .setCodeState c f => .setCodeState (Expr.rename c) (Expr.rename f)
  | .readings e lit alts => .readings e (Stmt.rename lit) (Stmt.renameAlts alts)
  | .findSuchThat x ty c r f => .findSuchThat (σ x) (TyExpr.rename ty) (Cond.rename c) r (Stmt.rename f)
  | .letSuchThat xs c objs => .letSuchThat (xs.map σ) (Cond.rename c) (Stmt.renameObjs objs)
  | .macro m as => .macro m (Expr.renameL as)
  | .phrase p hs => .phrase p (Hole.renameL hs)
  | .prose ch ps => .prose ch (Part.renameL ps)
  | .withSteps s ns => .withSteps (Stmt.rename s) (Node.renameL ns)
  | .expanded m as ns => .expanded m (Expr.renameL as) (Node.renameL ns)
  | s => s

def Stmt.renameRet : Option Expr → Option Expr
  | none => none
  | some e => some (Expr.rename e)

def Stmt.renameAlt : Reading × List Node → Reading × List Node
  | (q, ns) => (q, Node.renameL ns)

def Stmt.renameAlts : List (Reading × List Node) → List (Reading × List Node)
  | [] => []
  | a :: as => Stmt.renameAlt a :: Stmt.renameAlts as

def Stmt.renameObj : Bool × Expr → Bool × Expr
  | (mx, e) => (mx, Expr.rename e)

def Stmt.renameObjs : List (Bool × Expr) → List (Bool × Expr)
  | [] => []
  | o :: os => Stmt.renameObj o :: Stmt.renameObjs os

def Node.rename : Node → Node
  | .mk atss s => .mk atss (Stmt.rename s)

def Node.renameL : List Node → List Node
  | [] => []
  | n :: ns => Node.rename n :: Node.renameL ns

def Arm.rename : Arm → Arm
  | .mk atss c b => .mk atss (Cond.renameO c) (Body.rename b)

def Arm.renameL : List Arm → List Arm
  | [] => []
  | a :: as => Arm.rename a :: Arm.renameL as

def Arm.renameO : Option Arm → Option Arm
  | none => none
  | some a => some (Arm.rename a)
end

end Rename

/-- A macro use's expansion: algorithm `m`'s second definition (`⟨m.clause, 1⟩`), the steps the
first one's `<emu-alg>` stands for, over its parameters only, with parameter `i` renamed to the
variable `args[i]`; none for an argument that is not a variable. -/
def expansion (look : AlgId → Option Alg) (m : AlgId) (args : List Expr) : Option (List Node) := do
  let g ← look ⟨m.clause, 1⟩
  let xs ← args.mapM fun | .var x => some x | _ => none
  if g.vars.size == xs.length && g.closures.isEmpty then
    some (Node.renameL (fun i => xs.getD i i) g.body)
  else none

section Expand
variable (look : AlgId → Option Alg)

mutual
/-- `s` with each macro use that has an expansion (`expansion`) carrying it. -/
def Stmt.expand : Stmt → Stmt
  | .macro m as => match expansion look m as with
    | some ns => .expanded m as ns
    | none => .macro m as
  | .if_ c b arms els => .if_ c (Body.expand b) (Arm.expandL arms) (Arm.expandO els)
  | .ifElse c s1 s2 => .ifElse c (Stmt.expand s1) (Stmt.expand s2)
  | .repeat_ b => .repeat_ (Node.expandL b)
  | .repeatWhile c b => .repeatWhile c (Node.expandL b)
  | .repeatUntil c b => .repeatUntil c (Node.expandL b)
  | .forEach x ty l rev b => .forEach x ty l rev (Body.expand b)
  | .forEachRec fs x l b => .forEachRec fs x l (Body.expand b)
  | .forRange x lo li hi hi' desc b => .forRange x lo li hi hi' desc (Body.expand b)
  | .forSuchThat x ty c o b => .forSuchThat x ty c o (Body.expand b)
  | .forKeys x o c order b => .forKeys x o c order (Body.expand b)
  | .forIndex x l b => .forIndex x l (Body.expand b)
  | .forChildren x b => .forChildren x (Body.expand b)
  | .forChildrenOf x e b => .forChildrenOf x e (Body.expand b)
  | .repeatN e b => .repeatN e (Node.expandL b)
  | .readings e lit alts => .readings e (Stmt.expand lit) (Stmt.expandAlts alts)
  | .findSuchThat x ty c r f => .findSuchThat x ty c r (Stmt.expand f)
  | s => s

def Stmt.expandAlt : Reading × List Node → Reading × List Node
  | (q, ns) => (q, Node.expandL ns)

def Stmt.expandAlts : List (Reading × List Node) → List (Reading × List Node)
  | [] => []
  | a :: as => Stmt.expandAlt a :: Stmt.expandAlts as

def Body.expand : Body → Body
  | .inline s => .inline (Stmt.expand s)
  | .block ns => .block (Node.expandL ns)

def Node.expand : Node → Node
  | .mk atss s => .mk atss (Stmt.expand s)

def Node.expandL : List Node → List Node
  | [] => []
  | n :: ns => Node.expand n :: Node.expandL ns

def Arm.expand : Arm → Arm
  | .mk atss c b => .mk atss c (Body.expand b)

def Arm.expandL : List Arm → List Arm
  | [] => []
  | a :: as => Arm.expand a :: Arm.expandL as

def Arm.expandO : Option Arm → Option Arm
  | none => none
  | some a => some (Arm.expand a)
end

/-- A closure literal with its macro uses expanded. -/
def CloLit.expandMacros (c : CloLit) : CloLit := { c with body := Node.expandL look c.body }

/-- An algorithm with its macro uses expanded, in its steps and its closures. -/
def Alg.expandMacros (g : Alg) : Alg :=
  { g with body := Node.expandL look g.body, closures := g.closures.map (CloLit.expandMacros look) }

/-- An SDO row with its macro uses expanded, in its steps and its closures. -/
def SdoRow.expandMacros (r : SdoRow) : SdoRow :=
  { r with body := Node.expandL look r.body, closures := r.closures.map (CloLit.expandMacros look) }

end Expand


end Ecma
