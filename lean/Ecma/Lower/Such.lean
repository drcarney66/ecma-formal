module

public import Ecma.Ops.ProgPrim
public import Ecma.Lower.PhraseCalls

@[expose] public section

/-!
# Binding conditions expanded

`Prog.expandSuch`: each `If` or `Else if` whose condition binds a variable (`Cond.binder?`) and whose
phrase means an algorithm `a` becomes `Let t be a(holes, subject).`, then a branch on `t`: one value,
the consequent with `Let x be t[0].` first; none, the alternative; more, the residue primitive's call
(`sArmSuch`). An `Else if` site becomes an `Else` whose steps are that `Let` and an `If` of the arms
after it. `t` is one slot appended to the algorithm's or SDO row's variables, shared by its sites
and closures. A site that is another statement's part (an `Else`'s, a reading's pinned step) is
searched but not replaced; a phrase with another meaning, or a hole that is code, stays. An early-error
rule's condition reads a binding condition as a Boolean: its algorithm becomes a predicate call
(`Such.cond`), the subject last.
-/

namespace Ecma

namespace Such
variable (ph : PhraseId → PhraseMeaning) (t : Slot)

/-- A binding condition's variable, and its phrase's algorithm called on the holes, then the subject. -/
def call? (c : Cond) : Option (Slot × Expr) := do
  let (e, p, hs, x) ← c.binder?
  match ph p with
  | .alg a => return (x, .call (.alg a) ((← Hole.args? hs) ++ [e]))
  | _ => none

/-- The integer `k`. -/
def num (k : Nat) : Expr := .math .none (.num (.dec k))

/-- The number of values in `t`. -/
def len : Expr := .call (.prim Known.pListLen) [.var t]

/-- The test of the values in `t`: one, true; none, false; more, a residue. -/
def test : Cond :=
  .or .plain [.rel .eq (len t) (num 1), .and .plain [.rel .ne (len t) (num 0), .expr (.call (.prim resPrim) [])]]

/-- `Let t be e.` -/
def letStep (e : Expr) : Node := .mk [] (.let_ t e)

/-- A consequent with `Let x be t[0].` first. -/
def bindBody (x : Slot) : Body → Body
  | .inline s => .block [.mk [] (.let_ x (.index (.var t) (num 0))), .mk [] s]
  | .block ns => .block (.mk [] (.let_ x (.index (.var t) (num 0))) :: ns)

/-- Whether `s` is a site: an `If` whose condition is a binding condition with a call. -/
def site? : Stmt → Bool
  | .if_ c .. => (call? ph c).isSome
  | _ => false

mutual
/-- A step with its sites expanded: a site becomes its `Let` and its `If`; a statement's part stays. -/
def node : List Attr → Stmt → List Node
  | atts, .if_ c b arms els =>
    let (as, el) := arms' arms (armO els)
    match call? ph c with
    | some (x, e) => [letStep t e, .mk atts (.if_ (test t) (bindBody t x (body b)) as el)]
    | none => [.mk atts (.if_ c (body b) as el)]
  | atts, .ifElse c s1 s2 => [.mk atts (.ifElse c (match node [] s1 with
      | [.mk _ s'] => s'
      | _ => s1) (match node [] s2 with
      | [.mk _ s'] => s'
      | _ => s2))]
  | atts, .repeat_ b => [.mk atts (.repeat_ (nodes b))]
  | atts, .repeatWhile c b => [.mk atts (.repeatWhile c (nodes b))]
  | atts, .repeatUntil c b => [.mk atts (.repeatUntil c (nodes b))]
  | atts, .forEach x ty l rev b => [.mk atts (.forEach x ty l rev (body b))]
  | atts, .forEachRec fs x l b => [.mk atts (.forEachRec fs x l (body b))]
  | atts, .forRange x lo li hi hi' desc b => [.mk atts (.forRange x lo li hi hi' desc (body b))]
  | atts, .forSuchThat x ty c o b => [.mk atts (.forSuchThat x ty c o (body b))]
  | atts, .forKeys x o c order b => [.mk atts (.forKeys x o c order (body b))]
  | atts, .forIndex x l b => [.mk atts (.forIndex x l (body b))]
  | atts, .forChildren x b => [.mk atts (.forChildren x (body b))]
  | atts, .forChildrenOf x e b => [.mk atts (.forChildrenOf x e (body b))]
  | atts, .repeatN e b => [.mk atts (.repeatN e (nodes b))]
  | atts, .readings e lit alts => [.mk atts (.readings e (match node [] lit with
      | [.mk _ s'] => s'
      | _ => lit) (alts' alts))]
  | atts, .findSuchThat x ty c r f => [.mk atts (.findSuchThat x ty c r (match node [] f with
      | [.mk _ s'] => s'
      | _ => f))]
  | atts, .withSteps s ns => [.mk atts (.withSteps s (nodes ns))]
  | atts, .expanded m as ns => [.mk atts (.expanded m as (nodes ns))]
  | atts, s => [.mk atts s]

/-- Steps with their sites expanded, in place. -/
def nodes : List Node → List Node
  | [] => []
  | .mk atts s :: ns => node atts s ++ nodes ns

/-- A body; a sole step that is a site becomes a block. -/
def body : Body → Body
  | .inline s => match node [] s with
    | [.mk _ s'] => .inline s'
    | ns => .block ns
  | .block ns => .block (nodes ns)

/-- An `If`'s `Else if` steps before its `Else` `el`; from the first site, an `Else` of its `Let` and `If`. -/
def arms' : List Arm → Option Arm → List Arm × Option Arm
  | [], el => ([], el)
  | .mk atts (some c) b :: as, el => match call? ph c with
    | some (x, e) =>
      let (as', el') := arms' as el
      ([], some (.mk atts none (.block [letStep t e, .mk [] (.if_ (test t) (bindBody t x (body b)) as' el')])))
    | none => let (as', el') := arms' as el; (.mk atts (some c) (body b) :: as', el')
  | .mk atts none b :: as, el => let (as', el') := arms' as el; (.mk atts none (body b) :: as', el')

/-- An `Else` step expanded. -/
def armO : Option Arm → Option Arm
  | none => none
  | some (.mk atts c b) => some (.mk atts c (body b))

/-- An erratum's reading with its steps expanded. -/
def alt' : Reading × List Node → Reading × List Node
  | (q, ns) => (q, nodes ns)

/-- An erratum's readings with their steps expanded. -/
def alts' : List (Reading × List Node) → List (Reading × List Node)
  | [] => []
  | a :: as => alt' a :: alts' as
end

mutual
/-- How many sites a step and its nested steps have, the ones `node` replaces. -/
def sitesS : Stmt → Nat
  | .if_ c b arms els => (if (call? ph c).isSome then 1 else 0) + sitesB b + sitesA arms + sitesO els
  | .ifElse _ s1 s2 => (if site? ph s1 then 0 else sitesS s1) + (if site? ph s2 then 0 else sitesS s2)
  | .repeat_ b | .repeatWhile _ b | .repeatUntil _ b | .repeatN _ b | .withSteps _ b | .expanded _ _ b => sitesN b
  | .forEach _ _ _ _ b | .forEachRec _ _ _ b | .forRange _ _ _ _ _ _ b | .forSuchThat _ _ _ _ b | .forKeys _ _ _ _ b
  | .forIndex _ _ b | .forChildren _ b | .forChildrenOf _ _ b => sitesB b
  | .readings _ lit alts => (if site? ph lit then 0 else sitesS lit) + sitesAlts alts
  | .findSuchThat _ _ _ _ f => if site? ph f then 0 else sitesS f
  | _ => 0

/-- The sites of steps. -/
def sitesN : List Node → Nat
  | [] => 0
  | .mk _ s :: ns => sitesS s + sitesN ns

/-- The sites of a body. -/
def sitesB : Body → Nat
  | .inline s => sitesS s
  | .block ns => sitesN ns

/-- The sites of `Else if` steps, their conditions included. -/
def sitesA : List Arm → Nat
  | [] => 0
  | .mk _ c b :: as => (match c with
    | some c => if (call? ph c).isSome then 1 else 0
    | none => 0) + sitesB b + sitesA as

/-- The sites of an `Else` step. -/
def sitesO : Option Arm → Nat
  | none => 0
  | some (.mk _ _ b) => sitesB b

/-- The sites of an erratum's readings. -/
def sitesAlts : List (Reading × List Node) → Nat
  | [] => 0
  | (_, ns) :: as => sitesN ns + sitesAlts as
end

/-- The sites of steps and their closures. -/
def sitesOf (body : List Node) (cs : Array CloLit) : Nat :=
  sitesN ph body + cs.foldl (fun n c => n + sitesN ph c.body) 0

/-- A closure literal with its sites expanded, `t` its owner's slot. -/
def clo (c : CloLit) : CloLit := { c with body := nodes ph t c.body }

/-- A binding condition read as a Boolean: its phrase's algorithm as a predicate call on the holes. -/
def cond (c : Cond) : Cond :=
  match c.binder? with
  | some (e, p, hs, _) => match ph p, Hole.args? hs with
    | .alg a, some xs => .preds e (.call (.alg a) xs false) []
    | _, _ => c
  | none => c

mutual
/-- An early-error sentence with its conditions' binding conditions as calls (`cond`). -/
def early : EarlySentence → EarlySentence
  | .syntaxError e c u => .syntaxError e (cond ph c) (earlyU u)
  | .syntaxErrorIns c d => .syntaxErrorIns (cond ph c) (cond ph d)
  | .ifInline c s => .ifInline (cond ph c) (early s)
  | .forEachIn x ty l c s => .forEachIn x ty l (cond ph c) s
  | .notApplied c s => .notApplied (cond ph c) s
  | .layout raw ss => .layout raw (earlyL ss)
  | .readings e lit alts => .readings e (earlyL lit) (earlyAlts alts)
  | s => s

/-- A sentence's exception, its condition expanded. -/
def earlyU : Option (UnlessForm × Cond) → Option (UnlessForm × Cond)
  | none => none
  | some (f, d) => some (f, cond ph d)

/-- Early-error sentences expanded. -/
def earlyL : List EarlySentence → List EarlySentence
  | [] => []
  | s :: ss => early s :: earlyL ss

/-- An erratum's readings of early-error sentences expanded. -/
def earlyAlts : List (Reading × List EarlySentence) → List (Reading × List EarlySentence)
  | [] => []
  | (q, ss) :: rest => (q, earlyL ss) :: earlyAlts rest
end

end Such

variable (ph : PhraseId → PhraseMeaning)

/-- An algorithm with its binding conditions expanded, one slot appended where it has any. -/
def Alg.expandSuch (g : Alg) : Alg :=
  if Such.sitesOf ph g.body g.closures == 0 then g else
  { g with vars := g.vars.push "values", body := Such.nodes ph g.vars.size g.body,
           closures := g.closures.map (Such.clo ph g.vars.size) }

/-- An SDO row with its binding conditions expanded, one slot appended where it has any. -/
def SdoRow.expandSuch (r : SdoRow) : SdoRow :=
  if Such.sitesOf ph r.body r.closures == 0 then r else
  { r with vars := r.vars.push "values", body := Such.nodes ph r.vars.size r.body,
           closures := r.closures.map (Such.clo ph r.vars.size) }

/-- An early-error row with its binding conditions as calls. -/
def EarlyRow.expandSuch (r : EarlyRow) : EarlyRow := { r with body := Such.earlyL ph r.body }

/-- `P` with its algorithms', SDO rows' and early-error rows' binding conditions expanded over its phrase meanings. -/
def Prog.expandSuch (P : Prog) : Prog :=
  { P with
    alg := fun a => (P.alg a).map (Alg.expandSuch P.phrase)
    row := fun s k => (P.row s k).map (SdoRow.expandSuch P.phrase)
    rowOf := fun a => (P.rowOf a).map (SdoRow.expandSuch P.phrase)
    early := fun k => (P.early k).map (EarlyRow.expandSuch P.phrase) }

end Ecma
