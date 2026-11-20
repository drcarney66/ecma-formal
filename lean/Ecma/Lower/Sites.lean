module

public import Ecma.Notation.Early
public import Ecma.Notation.Tables
public import Ecma.Ops.Unchecked

@[expose] public section

/-!
# Phrase sites

`Sites`: what a pass makes of a phrase, per position (expression, condition, predicate, type,
statement step, mutation), given the phrase and its holes already rewritten, of a lone predicate
phrase with its subject, of one under a type (`ty`: the type's test, then the subject call), of a type
variable, of prose (as an expression, a checked condition or a step), of a step with nested steps its
form does not take, of `Throw` and of `For each … such that`, and whether an unchecked condition becomes
its key (`un`, `Cond.pass`); `none` keeps it. `Expr.rw` … `Arm.rwO`: the syntax with every site
rewritten, bottom-up, a place phrase a site rewrites as the field it writes (`Place.ofSite`);
`EarlySentence.rw`: an early-error rule's; `Table.rw`: a table's cells'. The contents
of a type or condition hole (a value the program carries) and a step whose nested steps its form does not
take are kept as written.
-/

namespace Ecma

/-- What a pass makes of a phrase at each position; `none` keeps it. -/
structure Sites where
  e : PhraseId → List Hole → Option Expr := fun _ _ => none
  c : PhraseId → List Hole → Option Cond := fun _ _ => none
  p : PhraseId → List Hole → Option Pred := fun _ _ => none
  t : PhraseId → List Hole → Option TyExpr := fun _ _ => none
  s : PhraseId → List Hole → Option Stmt := fun _ _ => none
  m : PhraseId → List Hole → Option Stmt := fun _ _ => none
  cp : Expr → PhraseId → List Hole → Option Cond := fun _ _ _ => none
  ty : Expr → AltForm → TyExpr → Bool := fun _ _ _ => false
  tv : String → Slot → Option TyExpr := fun _ _ => none
  pr : Channel → List Part → Option Expr := fun _ _ => none
  ws : Stmt → Option Stmt := fun _ => none
  te : ErrorId → Option Stmt := fun _ => none
  fst : Option Stmt := none
  un : Bool := false

/-- A place phrase `e` given its site's expression `o`: the field it writes, else `o`, else `e`. -/
def Place.ofSite (o : Option Expr) (e : Expr) : Place :=
  match o, e.fieldPlace? with
  | some _, some (f, s) => .field s f
  | some x, none => .expr x
  | none, _ => .expr e

section Rw
variable (σ : Sites)

/-- A subject and its predicates, rewritten: a lone predicate phrase, alone or under a type `ty` lifts, by `cp`. -/
def Sites.preds (e : Expr) (p : Pred) (rest : List (Conj × Pred)) : Cond :=
  match p, rest with
  | .phrase q hs, [] => (σ.cp e q hs).getD (.preds e p [])
  | .isTy false f [.that t (.phrase q hs) []], [] => match σ.cp e q hs with
    | some c => if σ.ty e f t then .and .plain [.preds e (.isTy false f [t]) [], c] else .preds e p []
    | none => .preds e p []
  | p, rest => .preds e p rest

mutual
/-- `e` with its sites rewritten. -/
def Expr.rw : Expr → Expr
  | .call f as => .call f (Expr.rwL as)
  | .callAt a as => .callAt a (Expr.rwL as)
  | .sdo s a e as => .sdo s a (Expr.rw e) (Expr.rwL as)
  | .component c a e => .component c a (Expr.rw e)
  | .field e f => .field (Expr.rw e) f
  | .imethod e m as => .imethod (Expr.rw e) m (Expr.rwL as)
  | .cmethod e m as => .cmethod (Expr.rw e) m (Expr.rwL as)
  | .apply f as => .apply (Expr.rw f) (Expr.rwL as)
  | .index e i => .index (Expr.rw e) (Expr.rw i)
  | .q e => .q (Expr.rw e)
  | .bang e => .bang (Expr.rw e)
  | .bangAt r e => .bangAt r (Expr.rw e)
  | .erratum r s e => .erratum r s (Expr.rw e)
  | .un o e => .un o (Expr.rw e)
  | .bin o a b => .bin o (Expr.rw a) (Expr.rw b)
  | .paren e => .paren (Expr.rw e)
  | .list es => .list (Expr.rwL es)
  | .record a k fs => .record a k (Expr.rwFs fs)
  | .resumedWith e => .resumedWith (Expr.rw e)
  | .childOf e n s => .childOf (Expr.rw e) n s
  | .annot ats e => .annot ats (Expr.rw e)
  | .tableStep t k x => .tableStep t (Expr.rw k) x
  | .extreme mx x ty c => .extreme mx x (TyExpr.rw ty) (Cond.rw c)
  | .phrase p hs => (σ.e p (Hole.rwL hs)).getD (.phrase p (Hole.rwL hs))
  | .prose ch ps => (σ.pr ch (Part.rwL ps)).getD (.prose ch (Part.rwL ps))
  | .ofCond c => .ofCond (Cond.rw c)
  | e => e

def Expr.rwL : List Expr → List Expr
  | [] => []
  | e :: es => Expr.rw e :: Expr.rwL es

def Expr.rwF : FieldId × Expr → FieldId × Expr
  | (f, e) => (f, Expr.rw e)

def Expr.rwFs : List (FieldId × Expr) → List (FieldId × Expr)
  | [] => []
  | fe :: fs => Expr.rwF fe :: Expr.rwFs fs

def Pred.rw : Pred → Pred
  | .isVal neg f vs => .isVal neg f (Expr.rwL vs)
  | .isTy neg f ts => .isTy neg f (TyExpr.rwL ts)
  | .phrase p hs => (σ.p p (Hole.rwL hs)).getD (.phrase p (Hole.rwL hs))
  | .call f as neg => .call f (Expr.rwL as) neg

def Pred.rwR : Conj × Pred → Conj × Pred
  | (j, p) => (j, Pred.rw p)

def Pred.rwRs : List (Conj × Pred) → List (Conj × Pred)
  | [] => []
  | r :: rs => Pred.rwR r :: Pred.rwRs rs

def Cond.rw : Cond → Cond
  | .preds e p rest => σ.preds (Expr.rw e) (Pred.rw p) (Pred.rwRs rest)
  | .rel o a b => .rel o (Expr.rw a) (Expr.rw b)
  | .and f cs => .and f (Cond.rwL cs)
  | .or f cs => .or f (Cond.rwL cs)
  | .paren c => .paren (Cond.rw c)
  | .alg a => .alg a
  | .phrase p hs => (σ.c p (Hole.rwL hs)).getD (.phrase p (Hole.rwL hs))
  | .prose ch ps =>
    if (Cond.prose ch ps).unchecked then
      if σ.un then .pass (Cond.prose ch ps).proseKey else .prose ch (Part.rwL ps)
    else ((σ.pr ch (Part.rwL ps)).map .expr).getD (.prose ch (Part.rwL ps))
  | .expr e => .expr (Expr.rw e)
  | .pass k => .pass k

def Cond.rwL : List Cond → List Cond
  | [] => []
  | c :: cs => Cond.rw c :: Cond.rwL cs

def Cond.rwO : Option Cond → Option Cond
  | none => none
  | some c => some (Cond.rw c)

def TyExpr.rw : TyExpr → TyExpr
  | .listOf a t => .listOf a (TyExpr.rw t)
  | .union f c ts => .union f c (TyExpr.rwL ts)
  | .interval t lo hi => .interval (TyExpr.rw t) (Expr.rw lo) (Expr.rw hi)
  | .value v => .value (Expr.rw v)
  | .that t p rest => .that (TyExpr.rw t) (Pred.rw p) (Pred.rwRs rest)
  | .phrase p hs => (σ.t p (Hole.rwL hs)).getD (.phrase p (Hole.rwL hs))
  | .var a x => (σ.tv a x).getD (.var a x)
  | .completion t => .completion (TyExpr.rwO t)
  | .record fs => .record (TyExpr.rwFs fs)
  | .prose ps => .prose (Part.rwL ps)
  | .pred p => .pred (Pred.rw p)
  | t => t

def TyExpr.rwL : List TyExpr → List TyExpr
  | [] => []
  | t :: ts => TyExpr.rw t :: TyExpr.rwL ts

def TyExpr.rwO : Option TyExpr → Option TyExpr
  | none => none
  | some t => some (TyExpr.rw t)

def TyExpr.rwF : FieldId × TyExpr → FieldId × TyExpr
  | (f, t) => (f, TyExpr.rw t)

def TyExpr.rwFs : List (FieldId × TyExpr) → List (FieldId × TyExpr)
  | [] => []
  | ft :: fs => TyExpr.rwF ft :: TyExpr.rwFs fs

def Hole.rw : Hole → Hole
  | .e x => .e (Expr.rw x)
  | .c x => .c (Cond.rw x)
  | .l f xs => .l f (Expr.rwL xs)
  | h => h

def Hole.rwL : List Hole → List Hole
  | [] => []
  | h :: hs => Hole.rw h :: Hole.rwL hs

def Part.rw : Part → Part
  | .text s => .text s
  | .hole h => .hole (Hole.rw h)

def Part.rwL : List Part → List Part
  | [] => []
  | p :: ps => Part.rw p :: Part.rwL ps

def Place.rw : Place → Place
  | .var x => .var x
  | .field e f => .field (Expr.rw e) f
  | .expr (.phrase p hs) => Place.ofSite (σ.e p (Hole.rwL hs)) (.phrase p (Hole.rwL hs))
  | .expr e => .expr (Expr.rw e)

def Body.rw : Body → Body
  | .inline s => .inline (Stmt.rw s)
  | .block ns => .block (Node.rwL ns)

def Stmt.rw : Stmt → Stmt
  | .let_ x e => .let_ x (Expr.rw e)
  | .letMany xs e v => .letMany xs (Expr.rw e) v
  | .set p e => .set (Place.rw p) (Expr.rw e)
  | .ret e => .ret (Stmt.rwRet e)
  | .perform e => .perform (Expr.rw e)
  | .if_ c b arms els => .if_ (Cond.rw c) (Body.rw b) (Arm.rwL arms) (Arm.rwO els)
  | .ifElse c s1 s2 => .ifElse (Cond.rw c) (Stmt.rw s1) (Stmt.rw s2)
  | .assert c => .assert (Cond.rw c)
  | .assertAt r c => .assertAt r (Cond.rw c)
  | .assertIf c d => .assertIf (Cond.rw c) (Cond.rw d)
  | .throwVal e => .throwVal (Expr.rw e)
  | .repeat_ b => .repeat_ (Node.rwL b)
  | .repeatWhile c b => .repeatWhile (Cond.rw c) (Node.rwL b)
  | .repeatUntil c b => .repeatUntil (Cond.rw c) (Node.rwL b)
  | .forEach x ty l rev b => .forEach x (TyExpr.rwO ty) (Expr.rw l) rev (Body.rw b)
  | .forEachRec fs x l b => .forEachRec fs x (Expr.rw l) (Body.rw b)
  | .forRange x lo li hi hi' desc b => .forRange x (Expr.rw lo) li (Expr.rw hi) hi' desc (Body.rw b)
  | .mutate p hs => (σ.m p (Hole.rwL hs)).getD (.mutate p (Hole.rwL hs))
  | .forSuchThat x ty c o b => σ.fst.getD (.forSuchThat x (TyExpr.rw ty) (Cond.rw c) o (Body.rw b))
  | .forKeys x o c order b => .forKeys x (Expr.rw o) (Cond.rw c) order (Body.rw b)
  | .forIndex x l b => .forIndex x (Expr.rw l) (Body.rw b)
  | .forChildren x b => .forChildren x (Body.rw b)
  | .forChildrenOf x e b => .forChildrenOf x (Expr.rw e) (Body.rw b)
  | .repeatN e b => .repeatN (Expr.rw e) (Node.rwL b)
  | .retSee e x => .retSee (Expr.rw e) x
  | .suspend c v => .suspend (Expr.rw c) v
  | .push c v => .push (Expr.rw c) v
  | .remove c v => .remove (Expr.rw c) v
  | .removeRestore c r => .removeRestore (Expr.rw c) (Expr.rw r)
  | .resumeLet c v x ats => .resumeLet (Expr.rw c) (Expr.rw v) x ats
  | .resume c v => .resume (Expr.rw c) (Expr.rw v)
  | .setCodeState c f => .setCodeState (Expr.rw c) (Expr.rw f)
  | .readings e lit alts => .readings e (Stmt.rw lit) (Stmt.rwAlts alts)
  | .findSuchThat x ty c r f => .findSuchThat x (TyExpr.rw ty) (Cond.rw c) r (Stmt.rw f)
  | .letSuchThat xs c objs => .letSuchThat xs (Cond.rw c) (Stmt.rwObjs objs)
  | .macro m as => .macro m (Expr.rwL as)
  | .phrase p hs => (σ.s p (Hole.rwL hs)).getD (.phrase p (Hole.rwL hs))
  | .prose ch ps => ((σ.pr ch (Part.rwL ps)).map .perform).getD (.prose ch (Part.rwL ps))
  | .expanded m as ns => .expanded m (Expr.rwL as) (Node.rwL ns)
  | .withSteps s x => (σ.ws (Stmt.rwW s)).getD (.withSteps s x)
  | .throwErr e => (σ.te e).getD (.throwErr e)
  | s => s

/-- The step of a `Stmt.withSteps`, its holes rewritten. -/
def Stmt.rwW : Stmt → Stmt
  | .phrase p hs => .phrase p (Hole.rwL hs)
  | .mutate p hs => .mutate p (Hole.rwL hs)
  | .prose ch ps => .prose ch (Part.rwL ps)
  | s => s

def Stmt.rwRet : Option Expr → Option Expr
  | none => none
  | some e => some (Expr.rw e)

def Stmt.rwAlt : Reading × List Node → Reading × List Node
  | (q, ns) => (q, Node.rwL ns)

def Stmt.rwAlts : List (Reading × List Node) → List (Reading × List Node)
  | [] => []
  | a :: as => Stmt.rwAlt a :: Stmt.rwAlts as

def Stmt.rwObj : Bool × Expr → Bool × Expr
  | (mx, e) => (mx, Expr.rw e)

def Stmt.rwObjs : List (Bool × Expr) → List (Bool × Expr)
  | [] => []
  | o :: os => Stmt.rwObj o :: Stmt.rwObjs os

def Node.rw : Node → Node
  | .mk atss s => .mk atss (Stmt.rw s)

def Node.rwL : List Node → List Node
  | [] => []
  | n :: ns => Node.rw n :: Node.rwL ns

def Arm.rw : Arm → Arm
  | .mk atss c b => .mk atss (Cond.rwO c) (Body.rw b)

def Arm.rwL : List Arm → List Arm
  | [] => []
  | a :: as => Arm.rw a :: Arm.rwL as

def Arm.rwO : Option Arm → Option Arm
  | none => none
  | some a => some (Arm.rw a)
end

/-- A closure literal with its sites rewritten. -/
def CloLit.rw (c : CloLit) : CloLit := { c with body := Node.rwL σ c.body }

/-- An algorithm with its sites rewritten, in its steps and its closures. -/
def Alg.rw (g : Alg) : Alg := { g with body := Node.rwL σ g.body, closures := g.closures.map (CloLit.rw σ) }

/-- An SDO row with its sites rewritten, in its steps and its closures. -/
def SdoRow.rw (r : SdoRow) : SdoRow := { r with body := Node.rwL σ r.body, closures := r.closures.map (CloLit.rw σ) }

mutual
/-- An early-error sentence with its sites rewritten. -/
def EarlySentence.rw : EarlySentence → EarlySentence
  | .syntaxError e c u => .syntaxError e (Cond.rw σ c) (EarlySentence.rwU u)
  | .syntaxErrorIns c d => .syntaxErrorIns (Cond.rw σ c) (Cond.rw σ d)
  | .mustCover p t => .mustCover (Expr.rw σ p) (TyExpr.rw σ t)
  | .ifInline c s => .ifInline (Cond.rw σ c) (EarlySentence.rw s)
  | .forEachIn x t l c s => .forEachIn x (TyExpr.rw σ t) (Expr.rw σ l) (Cond.rw σ c) (Stmt.rw σ s)
  | .notApplied c s => .notApplied (Cond.rw σ c) (Stmt.rw σ s)
  | .info s => .info (Stmt.rw σ s)
  | .stmt s => .stmt (Stmt.rw σ s)
  | .layout raw ss => .layout raw (EarlySentence.rwL ss)
  | .readings e lit alts => .readings e (EarlySentence.rwL lit) (EarlySentence.rwAlts alts)
  | s => s

def EarlySentence.rwU : Option (UnlessForm × Cond) → Option (UnlessForm × Cond)
  | none => none
  | some (f, d) => some (f, Cond.rw σ d)

def EarlySentence.rwL : List EarlySentence → List EarlySentence
  | [] => []
  | s :: ss => EarlySentence.rw s :: EarlySentence.rwL ss

def EarlySentence.rwAlts : List (Reading × List EarlySentence) → List (Reading × List EarlySentence)
  | [] => []
  | (q, ss) :: rest => (q, EarlySentence.rwL ss) :: EarlySentence.rwAlts rest
end

/-- An early-error rule row with its sites rewritten. -/
def EarlyRow.rw (r : EarlyRow) : EarlyRow := { r with body := EarlySentence.rwL σ r.body }

/-- A cell's type with its sites rewritten. -/
def TTy.rw : TTy → TTy
  | .ty t => .ty (TyExpr.rw σ t)
  | .records fs => .records (fs.map fun (f, t) => (f, TyExpr.rw σ t))

/-- A signature with its parameters' and result's types rewritten. -/
def Sig.rw (g : Sig) : Sig :=
  { g with params := g.params.map fun p => { p with ty := TTy.rw σ p.ty }, ret := TTy.rw σ g.ret }

mutual
/-- A table cell's content with its sites rewritten. -/
def CellBody.rw : CellBody → CellBody
  | .stmt s => .stmt (Stmt.rw σ s)
  | .expr e => .expr (Expr.rw σ e)
  | .ty t => .ty (TTy.rw σ t)
  | .sig g => .sig (Sig.rw σ g)
  | .lines cs => .lines (CellBody.rwL cs)
  | .dfn c => .dfn (CellBody.rw c)
  | .code c => .code (CellBody.rw c)
  | .link h c => .link h (CellBody.rw c)
  | c => c

def CellBody.rwL : List CellBody → List CellBody
  | [] => []
  | c :: cs => CellBody.rw c :: CellBody.rwL cs
end

/-- A table with its cells' sites rewritten. -/
def Table.rw (t : Table) : Table :=
  { t with rows := t.rows.map fun r => { r with cells := r.cells.map fun c => { c with body := CellBody.rw σ c.body } } }

end Rw

end Ecma
