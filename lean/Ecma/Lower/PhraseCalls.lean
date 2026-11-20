module

public import Ecma.Lower.Sites
public import Ecma.Host.Jobs

@[expose] public section

/-!
# Phrases as calls

`Expr.calls` rewrites each phrase at an expression, predicate, type, condition or step position into its
meaning's call: an algorithm's (at a Parse Node, `Expr.callAt`, where its steps may read the node:
`CallsCfg.atAlg`, decided by `Prog.nodeAlg`; such a phrase off a node stays), a primitive's on its arguments
(under `not` where it negates; an omitted optional part `.absent`, `PhraseArg.pad`), a predicate call (`Pred.call`,
the subject last) or a condition on a subject-first call; a phrase without a meaning
into the residue primitive's call on its holes, binding conditions dropped. A binding condition's phrase and one whose holes have no
such form or would be evaluated in another order stay; a place phrase's subject is rewritten
(`Place.ofSite`). Live prose becomes its primitive's call,
other prose the residue primitive's; a step with nested steps its form does not take becomes the residue
primitive's call on the holes it evaluates, `For each … such that` its call on none, `Throw` the error
algorithm's call, thrown, and an unchecked condition its key (`Cond.pass`). A type variable is left as
written. The traversal is `Sites`'.
-/

namespace Ecma

/-- A primitive id outside every table: no table declares it, so its call stops with a residue. -/
def resPrim : PrimId := 100000

/-- What the rewrite reads: each phrase's meaning, whether the steps run at a Parse Node, the algorithms
whose phrases run at one (`atAlg`), and the types false on *undefined* (`undefOut`). -/
structure CallsCfg where
  ph : PhraseId → PhraseMeaning
  atNode : Bool
  atAlg : AlgId → Bool := fun _ => false
  undefOut : List SortId → SortId → Bool := fun _ _ => false

section NodeFree
variable (free : PhraseId → Bool)

mutual
/-- An expression that reads no Parse Node of its steps', its phrases' calls by `free`; `false` where unsure. -/
def Expr.nodeFree : Expr → Bool
  | .var _ | .val _ | .math .. | .enum _ | .param _ | .intrinsic _ | .fieldName _ | .nt .. | .prod ..
  | .codeUnit .. | .codePoint .. | .code .. | .term _ | .thisValue _ | .newTarget | .xref _ | .closure _
  | .table .. | .definition .. | .bnd _ | .data _ => true
  | .call _ as | .list as => Expr.nodeFreeL as
  | .sdo _ _ e as | .imethod e _ as | .cmethod e _ as | .apply e as => Expr.nodeFree e && Expr.nodeFreeL as
  | .component _ _ e | .field e _ | .q e | .bang e | .bangAt _ e | .erratum _ _ e | .un _ e | .paren e
  | .resumedWith e | .childOf e .. | .annot _ e => Expr.nodeFree e
  | .index a b | .bin _ a b => Expr.nodeFree a && Expr.nodeFree b
  | .record _ _ fs => Expr.nodeFreeFs fs
  | .phrase p hs => free p && Hole.nodeFreeL hs
  | .prose _ ps => Part.nodeFreeL ps
  | .ofCond c => Cond.nodeFree c
  | _ => false

def Expr.nodeFreeL : List Expr → Bool
  | [] => true
  | e :: es => Expr.nodeFree e && Expr.nodeFreeL es

def Expr.nodeFreeF : FieldId × Expr → Bool
  | (_, e) => Expr.nodeFree e

def Expr.nodeFreeFs : List (FieldId × Expr) → Bool
  | [] => true
  | fe :: fs => Expr.nodeFreeF fe && Expr.nodeFreeFs fs

def Pred.nodeFree : Pred → Bool
  | .isVal _ _ vs | .call _ vs _ => Expr.nodeFreeL vs
  | .isTy _ _ ts => TyExpr.nodeFreeL ts
  | .phrase p hs => free p && Hole.nodeFreeL hs

def Pred.nodeFreeR : Conj × Pred → Bool
  | (_, p) => Pred.nodeFree p

def Pred.nodeFreeRs : List (Conj × Pred) → Bool
  | [] => true
  | r :: rs => Pred.nodeFreeR r && Pred.nodeFreeRs rs

def Cond.nodeFree : Cond → Bool
  | .preds e p rest => Expr.nodeFree e && Pred.nodeFree p && Pred.nodeFreeRs rest
  | .rel _ a b => Expr.nodeFree a && Expr.nodeFree b
  | .and _ cs | .or _ cs => Cond.nodeFreeL cs
  | .paren c => Cond.nodeFree c
  | .phrase p hs => free p && Hole.nodeFreeL hs
  | .prose _ ps => Part.nodeFreeL ps
  | .expr e => Expr.nodeFree e
  | .pass _ => true
  | .alg _ => false

def Cond.nodeFreeL : List Cond → Bool
  | [] => true
  | c :: cs => Cond.nodeFree c && Cond.nodeFreeL cs

def TyExpr.nodeFree : TyExpr → Bool
  | .sort .. | .var .. | .nt .. => true
  | .listOf _ t => TyExpr.nodeFree t
  | .union _ _ ts => TyExpr.nodeFreeL ts
  | .interval t lo hi => TyExpr.nodeFree t && Expr.nodeFree lo && Expr.nodeFree hi
  | .value v => Expr.nodeFree v
  | .that t p rest => TyExpr.nodeFree t && Pred.nodeFree p && Pred.nodeFreeRs rest
  | .phrase p hs => free p && Hole.nodeFreeL hs
  | .prose ps => Part.nodeFreeL ps
  | .pred p => Pred.nodeFree p
  | _ => false

def TyExpr.nodeFreeL : List TyExpr → Bool
  | [] => true
  | t :: ts => TyExpr.nodeFree t && TyExpr.nodeFreeL ts

def Hole.nodeFree : Hole → Bool
  | .e x => Expr.nodeFree x
  | .c x => Cond.nodeFree x
  | .t (.sort _ [] _ _) | .b _ | .w _ | .text _ | .field _ => true
  | .l _ xs => Expr.nodeFreeL xs
  | _ => false

def Hole.nodeFreeL : List Hole → Bool
  | [] => true
  | h :: hs => Hole.nodeFree h && Hole.nodeFreeL hs

def Part.nodeFree : Part → Bool
  | .text _ => true
  | .hole h => Hole.nodeFree h

def Part.nodeFreeL : List Part → Bool
  | [] => true
  | p :: ps => Part.nodeFree p && Part.nodeFreeL ps
end

mutual
/-- Steps that read no Parse Node of their own, their phrases' calls by `free`; `false` where unsure. -/
def Stmt.nodeFree : Stmt → Bool
  | .let_ _ e | .letMany _ e _ | .perform e | .throwVal e | .retSee e _ => Expr.nodeFree free e
  | .set (.var _) e => Expr.nodeFree free e
  | .set (.field l _) e | .set (.expr l) e => Expr.nodeFree free l && Expr.nodeFree free e
  | .ret none | .unreachable _ | .throwErr _ => true
  | .ret (some e) => Expr.nodeFree free e
  | .if_ c b arms els => Cond.nodeFree free c && Body.nodeFree b && Arm.nodeFreeL arms && Arm.nodeFreeO els
  | .ifElse c s₁ s₂ => Cond.nodeFree free c && Stmt.nodeFree s₁ && Stmt.nodeFree s₂
  | .assert c | .assertAt _ c => Cond.nodeFree free c
  | .assertIf c d => Cond.nodeFree free c && Cond.nodeFree free d
  | .repeat_ b => Node.nodeFreeL b
  | .repeatWhile c b | .repeatUntil c b => Cond.nodeFree free c && Node.nodeFreeL b
  | .forEach _ none l _ b | .forEachRec _ _ l b | .forIndex _ l b | .forChildrenOf _ l b =>
    Expr.nodeFree free l && Body.nodeFree b
  | .forRange _ lo _ hi _ _ b => Expr.nodeFree free lo && Expr.nodeFree free hi && Body.nodeFree b
  | .forKeys _ o c _ b => Expr.nodeFree free o && Cond.nodeFree free c && Body.nodeFree b
  | .repeatN e b => Expr.nodeFree free e && Node.nodeFreeL b
  | .phrase p hs | .mutate p hs => free p && Hole.nodeFreeL free hs
  | .prose _ ps => Part.nodeFreeL free ps
  | _ => false

def Body.nodeFree : Body → Bool
  | .inline s => Stmt.nodeFree s
  | .block ns => Node.nodeFreeL ns

def Node.nodeFree : Node → Bool
  | .mk _ s => Stmt.nodeFree s

def Node.nodeFreeL : List Node → Bool
  | [] => true
  | n :: ns => Node.nodeFree n && Node.nodeFreeL ns

def Arm.nodeFree : Arm → Bool
  | .mk _ none b => Body.nodeFree b
  | .mk _ (some c) b => Cond.nodeFree free c && Body.nodeFree b

def Arm.nodeFreeL : List Arm → Bool
  | [] => true
  | a :: as => Arm.nodeFree a && Arm.nodeFreeL as

def Arm.nodeFreeO : Option Arm → Bool
  | none => true
  | some a => Arm.nodeFree a
end

end NodeFree

/-- A phrase whose call reads no Parse Node: a primitive's without the node argument, an algorithm's by `af`,
the residue's. -/
def PhraseMeaning.callNodeFree (af : AlgId → Bool) : PhraseMeaning → Bool
  | .alg a => af a
  | .prim _ as _ => !as.contains .thisNode
  | .none => true

/-- An algorithm whose steps read no Parse Node, its phrases' meanings by `ph`, their algorithms' by `af`;
`false` where unsure. -/
def Alg.nodeFree (ph : PhraseId → PhraseMeaning) (af : AlgId → Bool) (g : Alg) : Bool :=
  Node.nodeFreeL (fun p => (ph p).callNodeFree af) g.body

/-- An expression whose value needs no step: a constant, a binder read, at a Parse Node the node. -/
def Expr.atom (atNode : Bool) : Expr → Bool
  | .bnd _ | .data _ | .fieldName _ | .code .. | .enum _ | .nt .. => true
  | .thisNode => atNode
  | .child k _ _ => atNode && k == 6
  | _ => false

/-- An expression hole's expression as a phrase reads it: a variable as a binder. -/
def Expr.asArg : Expr → Expr
  | .var x => .bnd x
  | e => e

/-- A phrase's hole as an expression, as `phraseH` reads it; none for a type or condition value. -/
def Hole.arg? : Hole → Option Expr
  | .e x => some x.asArg
  | .c x => some (.ofCond x)
  | .t (.sort _ [] s _) => some (.data (.sort s))
  | .t _ => none
  | .b x => some (.bnd x)
  | .bc .. => none
  | .w i => some (.data (.choice i))
  | .l _ xs => some (.list xs)
  | .text s => some (.code s "")
  | .field f => some (.fieldName f)

/-- A prose hole as an expression, as `evalH` reads it; none for a type or condition value. -/
def Hole.val? : Hole → Option Expr
  | .e x => some x
  | h => h.arg?

/-- Prose's holes as expressions (`evalParts`). -/
def Part.vals? : List Part → Option (List Expr)
  | [] => some []
  | .text _ :: ps => Part.vals? ps
  | .hole h :: ps => do return (← h.val?) :: (← Part.vals? ps)

/-- A phrase's holes as expressions (`evalPHs`). -/
def Hole.args? : List Hole → Option (List Expr)
  | [] => some []
  | h :: hs => do return (← h.arg?) :: (← Hole.args? hs)

/-- A hole other than a binding condition, which evaluates purely (`evalH`). -/
def Hole.notBc : Hole → Bool
  | .bc .. => false
  | _ => true

/-- A residue phrase's holes as expressions, its binding conditions dropped. -/
def Hole.resArgs? (hs : List Hole) : Option (List Expr) := Hole.args? (hs.filter Hole.notBc)

/-- A spreading phrase's holes as expressions (`evalSHs`): a list hole's elements in its place. -/
def Hole.spreadArgs? : List Hole → Option (List Expr)
  | [] => some []
  | h :: hs => match h with
    | .l _ xs => do return xs ++ (← Hole.spreadArgs? hs)
    | h => do return (← h.arg?) :: (← Hole.spreadArgs? hs)

/-- A primitive phrase's argument over its value expressions `es` (`phraseArg`); none for a hole out of
range, or the node away from a Parse Node. -/
def PhraseArg.exprs? (atNode : Bool) (es : List Expr) : PhraseArg → Option (List Expr)
  | .hole i => es[i]?.map ([·])
  | .spread i => some (es.drop i)
  | .enum e => some [.enum e]
  | .subject => es.getLast?.map ([·])
  | .thisNode => if atNode then some [.thisNode] else none
  | .sort s => some [.data (.sort s)]
  | .field f => some [.fieldName f]
  | .choice k => some [.data (.choice k)]

/-- A primitive phrase's arguments over its value expressions (`phraseArgs`). -/
def PhraseArg.argExprs? (atNode : Bool) (es : List Expr) : List PhraseArg → Option (List Expr)
  | [] => some []
  | a :: as => do return (← a.exprs? atNode es) ++ (← PhraseArg.argExprs? atNode es as)

/-- Past the value `es[i]`, the values from `es[j]` on read: the next position to read; none if a value
that needs a step is skipped or read twice. -/
def PhraseArg.past (atNode : Bool) (es : List Expr) (j i : Nat) : Option Nat :=
  if (es.getD i (.bnd 0)).atom atNode then some j
  else if j ≤ i && ((es.drop j).take (i - j)).all (·.atom atNode) then some (i + 1) else none

/-- The arguments read each value from `es[j]` on that needs a step once, in the values' order. -/
def PhraseArg.ordered (atNode : Bool) (es : List Expr) : Nat → List PhraseArg → Bool
  | j, [] => (es.drop j).all (·.atom atNode)
  | j, .hole i :: as => match PhraseArg.past atNode es j i with
    | some j' => PhraseArg.ordered atNode es j' as
    | none => false
  | j, .subject :: as => match PhraseArg.past atNode es j (es.length - 1) with
    | some j' => PhraseArg.ordered atNode es j' as
    | none => false
  | j, .spread i :: as =>
    (j ≤ i && ((es.drop j).take (i - j)).all (·.atom atNode)) && PhraseArg.ordered atNode es es.length as
  | j, _ :: as => PhraseArg.ordered atNode es j as

/-- The arguments read each value that needs a step once, in the values' order. -/
def PhraseArg.inOrder (atNode : Bool) (es : List Expr) (as : List PhraseArg) : Bool :=
  PhraseArg.ordered atNode es 0 as

/-- The variable a phrase's holes bind, as a binding condition reads them (`Cond.binder?`). -/
def Hole.bound? (hs : List Hole) : Option Slot := hs.findSome? fun | .b x => some x | _ => none

/-- An argument that names neither a predicate's subject nor a spread. -/
def PhraseArg.plain : PhraseArg → Bool
  | .subject | .spread _ => false
  | _ => true

/-- `.absent` for each hole plain arguments `as` read past the values `es`; none for a subject or spread. -/
def PhraseArg.pad (as : List PhraseArg) (es : List Expr) : List Expr :=
  if as.all PhraseArg.plain then
    List.replicate (as.foldr (fun a k => match a with | .hole i => max k (i + 1) | _ => k) 0 - es.length) (.data .absent)
  else []

/-- `e`, negated where `neg`. -/
def Expr.negIf (neg : Bool) (e : Expr) : Expr := if neg then .un .not e else e

/-- A primitive's call on the arguments `as` over the value expressions `es`, negated where `neg`. -/
def primCall? (atNode : Bool) (q : PrimId) (as : List PhraseArg) (neg : Bool) (es : List Expr) : Option Expr := do
  let xs ← PhraseArg.argExprs? atNode es as
  if PhraseArg.inOrder atNode es as then some (Expr.negIf neg (.call (.prim q) xs)) else none

/-- Prose as a call: a live channel's primitive on the holes, a residue channel's as the residue
primitive's call on none. -/
def proseCall? (ch : Channel) (ps : List Part) : Option Expr :=
  match ch.live? with
  | some q => (Part.vals? ps).map (.call (.prim q))
  | none => some (.call (.prim resPrim) [])

namespace CallsCfg
variable (c : CallsCfg)

/-- A phrase at an expression or condition position as a call, on its holes `hs`. -/
def phraseCall? (p : PhraseId) (hs : List Hole) : Option Expr :=
  match c.ph p with
  | .alg a =>
    if c.atAlg a then (if c.atNode then (Hole.args? hs).map (.callAt a) else none)
    else (Hole.args? hs).map (.call (.alg a))
  | .prim q as neg => do
    let es ← if (PhraseMeaning.prim q as neg).spreads then Hole.spreadArgs? hs else Hole.args? hs
    primCall? c.atNode q as neg (es ++ PhraseArg.pad as es)
  | .none => (Hole.resArgs? hs).map (.call (.prim resPrim))

/-- A predicate phrase as a predicate call, its subject last. -/
def predCall? (p : PhraseId) (hs : List Hole) : Option Pred :=
  match c.ph p with
  | .alg a => if c.atAlg a then none else (Hole.args? hs).map (.call (.alg a) · false)
  | .prim q as neg => match as.getLast? with
    | some .subject => do
      let as := as.dropLast
      if as.all PhraseArg.plain then
        let es ← Hole.args? hs
        let xs ← PhraseArg.argExprs? c.atNode es as
        if PhraseArg.inOrder c.atNode es as then some (.call (.prim q) xs neg) else none
      else none
    | _ => none
  | .none => (Hole.args? hs).map (.call (.prim resPrim) · false)

/-- A lone predicate phrase on the subject `e` whose primitive takes the subject first, as the call's
condition. -/
def subjCall? (e : Expr) (p : PhraseId) (hs : List Hole) : Option Cond :=
  match c.ph p with
  | .prim q (.subject :: as) neg =>
    if as.all PhraseArg.plain then do
      let es ← Hole.args? hs
      let xs ← PhraseArg.argExprs? c.atNode es as
      if PhraseArg.inOrder c.atNode es as then some (.expr (Expr.negIf neg (.call (.prim q) (e :: xs)))) else none
    else none
  | _ => none

/-- A variable's subject-first call lifts out of a type `a mods s` whose test is false on *undefined*. -/
def tyLift (e : Expr) (f : AltForm) : TyExpr → Bool
  | .sort _ mods s _ => e.slot?.isSome && f != .neither && c.undefOut mods s
  | _ => false

/-- A predicate phrase's call, none where a hole binds a variable (a binding condition's phrase). -/
def pred? (p : PhraseId) (hs : List Hole) : Option Pred :=
  if (Hole.bound? hs).isSome then none else c.predCall? p hs

/-- A lone predicate phrase's subject-first call, none where a hole binds a variable. -/
def subjFirst? (e : Expr) (p : PhraseId) (hs : List Hole) : Option Cond :=
  if (Hole.bound? hs).isSome then none else c.subjCall? e p hs

/-- A step with nested steps its form does not take (`Stmt.withSteps`), its holes rewritten: the
residue primitive's call on the holes the step evaluates. -/
def stepsCall? : Stmt → Option Stmt
  | .phrase p hs | .mutate p hs =>
    (if (c.ph p).spreads then Hole.spreadArgs? hs else Hole.args? hs).map fun es => .perform (.call (.prim resPrim) es)
  | .prose ch ps => match ch.live? with
    | some _ => (Part.vals? ps).map fun es => .perform (.call (.prim resPrim) es)
    | none => some (.perform (.call (.prim resPrim) []))
  | _ => some (.perform (.call (.prim resPrim) []))

/-- `Throw a … exception.`: the error phrase's algorithm on the error, thrown. -/
def errCall? (e : ErrorId) : Option Stmt :=
  match c.ph Known.phNewError with
  | .alg a => if c.atAlg a then none else some (.throwVal (.call (.alg a) [.fieldName e]))
  | _ => none

/-- The rewrite's sites: a phrase at an expression or condition position as its call, at a predicate
or type position as a predicate call, a lone predicate phrase taking its subject first as a condition (under
a type that lifts, after the type's test), a phrase
or mutation step as its call performed; prose as its call; the steps the machine runs as a residue as the
residue primitive's call; `Throw` as the error algorithm's call, thrown; an unchecked condition as its key. -/
def sites : Sites where
  e := c.phraseCall?
  c p hs := (c.phraseCall? p hs).map .expr
  p := c.pred?
  t p hs := (c.pred? p hs).map .pred
  cp := c.subjFirst?
  ty := c.tyLift
  s p hs := (c.phraseCall? p hs).map .perform
  m p hs := (c.phraseCall? p hs).map .perform
  pr := proseCall?
  ws := c.stepsCall?
  te := c.errCall?
  fst := some (.perform (.call (.prim resPrim) []))
  un := true

end CallsCfg

end Ecma
