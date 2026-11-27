module

public import Ecma.Lower.LinExpr
public import Ecma.Lower.LinEarly
public import Ecma.Lower.Src
public import Ecma.Lower.Expand

@[expose] public section

/-!
# `lin`: the program as the machine's code

Statements as code with step sites at the steps' paths (step `i :: up`, an `If`'s `Else if` and `Else`
steps after it, nested steps one level in); each unit's code, a
closure literal's under its literal's step; `lin s host`, the machine's program of `s.expanded host`.
-/

namespace Ecma.Machine
open Ecma

section Lin
variable (cx : Cx)

/-- The width of a step: an `If` numbers its `Else if` and `Else` steps after it. -/
def width : Stmt → Nat
  | .if_ _ _ arms els => 1 + arms.length + els.toList.length
  | _ => 1

/-- The path of the `j`th `Else if` or `Else` step after the step at `p`. -/
def armPath (p : List Nat) (j : Nat) : List Nat :=
  match p with
  | i :: up => (i + 1 + j) :: up
  | [] => []

mutual
/-- A statement at step path `p`. -/
def linS (p : List Nat) : Stmt → Code
  | .let_ x e => [.let_ x (linE cx e)]
  | .set (.var x) e => [.let_ x (linE cx e)]
  | .set (.field o f) e => [.setField f (linE cx o) (linE cx e)]
  | .set (.expr x) e => match x.fieldPlace?, x with
    | some (f, o), _ => [.setField f (linE cx o) (linE cx e)]
    | none, .index l i => [.setIndex (linE cx l) (linE cx i) (linE cx e)]
    | none, _ => [.residue "set"]
  | .ret none => [.retUnused]
  | .ret (some e) => [.ret (linE cx e)]
  | .perform e => [.eval (linE cx e)]
  | .if_ c b arms els => [.br (linC cx c) (linBody p b) (linArms p 0 arms (linEls p arms.length els))]
  | .ifElse c s1 s2 => [.br (linC cx c) (linS p s1) (linS p s2)]
  | .assert c => if c.unchecked then [] else [.assert (linC cx c)]
  | .assertAlways c => if c.unchecked then [] else [.assertAlways (linC cx c)]
  | .assertIf c d => match uncheckedIf c d with
    | some _ => []
    | none => [.assertIf (linC cx c) (linC cx d)]
  | .unreachable _ => [.stop .assertFailed]
  | .throwVal e => [.throw (linE cx e)]
  | .note _ => []
  | .repeat_ b => [.loop none .rep p (linNodes b 1 p)]
  | .repeatWhile c b => [.loop none (.while_ (linC cx c)) p (linNodes b 1 p)]
  | .repeatUntil c b => [.loop none (.until_ (linC cx c)) p (linNodes b 1 p)]
  | .forEach x _ l rev b => [.loop (some x) (.each (linE cx l) rev) p (linBody p b)]
  | .forEachRec _ x l b => [.loop (some x) (.each (linE cx l) false) p (linBody p b)]
  | .forRange x lo li hi hi' desc b =>
    [.loop (some x) (.range (linE cx lo) (linE cx hi) li hi' desc) p (linBody p b)]
  | .forKeys x o c order b => [.loop (some x) (.keys (linE cx o) order (linC cx c)) p (linBody p b)]
  | .forIndex x l b => [.loop (some x) (.idx (linE cx l)) p (linBody p b)]
  | .forChildren x b => [.loop (some x) (.kids none) p (linBody p b)]
  | .forChildrenOf x e b => [.loop (some x) (.kids (some (linE cx e))) p (linBody p b)]
  | .repeatN e b => [.loop none (.times (linE cx e)) p (linNodes b 1 p)]
  | .suspend e v => if v == 0 then [] else [.ctxRemove (linE cx e)]
  | .push e _ => [.ctxPush (linE cx e)]
  | .remove e _ => [.ctxRemove (linE cx e)]
  | .removeRestore e r => [.ctxRemove (linE cx e), .ctxTopIs (linE cx r)]
  | .resumeTop => []
  | .resumeLet e v x => [.transfer (some x) (linE cx e) (linE cx v)]
  | .resume e v => [.transfer none (linE cx e) (linE cx v)]
  | .setCodeState e f => [.setField Known.fCodeState (linE cx e) (linE cx f)]
  | .block ns => linNodes ns 1 p

/-- Steps from number `i` under `up`, each entered at its site. -/
def linNodes : List Stmt → Nat → List Nat → Code
  | [], _, _ => []
  | s :: ns, i, up => .site (i :: up) :: linS (i :: up) s ++ linNodes ns (i + width s) up

/-- A body at its step's path: an inline statement there, or steps one level in. -/
def linBody (p : List Nat) : Body → Code
  | .inline s => linS p s
  | .block ns => linNodes ns 1 p

/-- The `Else if` steps from the `j`th after the step at `p`, each entered at its site, then `last`. -/
def linArms (p : List Nat) (j : Nat) : List Arm → Code → Code
  | [], last => last
  | a :: as, last => linArm p j a (linArms p (j + 1) as last)

/-- The `Else` step, the `j`th after the step at `p`; none, nothing. -/
def linEls (p : List Nat) (j : Nat) : Option Arm → Code
  | none => []
  | some a => linArm p j a []

/-- The `j`th `Else if` or `Else` step after the step at `p`, the code after it `next` when its test fails. -/
def linArm (p : List Nat) (j : Nat) : Arm → Code → Code
  | .mk none b, _ => .site (armPath p j) :: linBody (armPath p j) b
  | .mk (some c) b, next => .site (armPath p j) :: [.br (linC cx c) (linBody (armPath p j) b) next]
end

end Lin

/-! Units. -/

mutual
/-- The closure literals an operand tree makes, in evaluation order. -/
def Op.clos : Op → List Nat
  | .closure k _ => [k]
  | .leaf _ as | .call _ as | .and as | .or as => Op.closL as
  | .on _ r as => Op.clos r ++ Op.closL as
  | .bind a b | .all a b => Op.clos a ++ Op.clos b
  | .andT cs t => Op.closL cs ++ Op.clos t
  | _ => []

def Op.closL : List Op → List Nat
  | [] => []
  | o :: os => Op.clos o ++ Op.closL os
end

/-- The closure literals an iterator's operands make. -/
def Iter.clos : Iter → List Nat
  | .while_ c | .until_ c | .each c _ | .idx c | .kids (some c) | .times c => c.clos
  | .range a b .. | .keys a _ b => a.clos ++ b.clos
  | _ => []

mutual
/-- Each closure literal the code makes, with the path of the step making it, in order. -/
def Code.cloSites (p : List Nat) : Code → List (Nat × List Nat)
  | [] => []
  | .site q :: is => Code.cloSites q is
  | i :: is => Ins.cloSites p i ++ Code.cloSites p is

def Ins.cloSites (p : List Nat) : Ins → List (Nat × List Nat)
  | .let_ _ e | .eval e | .ret e | .throw e | .ctxPush e | .ctxRemove e | .ctxTopIs e | .assert e
  | .assertAlways e => e.clos.map (·, p)
  | .setField _ a b | .transfer _ a b | .assertIf a b => (a.clos ++ b.clos).map (·, p)
  | .setIndex a b c => (a.clos ++ b.clos ++ c.clos).map (·, p)
  | .br c t e => c.clos.map (·, p) ++ Code.cloSites p t ++ Code.cloSites p e
  | .loop _ it _ b => it.clos.map (·, p) ++ Code.cloSites p b
  | _ => []
end

/-- An owner's closure literals' code: each under the path of the step making it, found in the owner's code
`top` or a closure's found before it; the first occurrence counts. -/
def cloUnits (P : Prog) (cls : Array CloLit) (top : Code) : Array (Option (List Nat × Code)) :=
  let cx : Cx := ⟨P, cls⟩
  let unit := fun (k : Nat) (q : List Nat) => (cls[k]?).map fun cl => (q, linNodes cx cl.body 1 q)
  let rec go : Nat → List (Nat × List Nat) → Array (Option (List Nat × Code)) → Array (Option (List Nat × Code))
    | 0, _, acc => acc
    | _ + 1, [], acc => acc
    | f + 1, (k, q) :: todo, acc =>
      if (acc[k]?).join.isSome then go f todo acc
      else match unit k q with
        | some u => go f (todo ++ Code.cloSites q u.2) (acc.setIfInBounds k (some u))
        | none => go f todo acc
  go (cls.size * cls.size + cls.size + 1) (Code.cloSites [] top) (Array.replicate cls.size none)

mutual
/-- A table cell as the values it holds (`CellCode`). -/
def cellCode (P : Prog) : CellBody → CellCode
  | .expr e => .vals [linE ⟨P, #[]⟩ e]
  | .name s => .vals [.const (.str s)]
  | .op c => .vals [.const (.alg ⟨c, 0⟩)]
  | .field f | .component f => .vals [.const (.fieldName f)]
  | .dfn c | .code c | .link _ c => .wrap (cellCode P c)
  | .lines cs => .lines (cellCodes P cs)
  | _ => .other

def cellCodes (P : Prog) : List CellBody → List CellCode
  | [] => []
  | c :: cs => cellCode P c :: cellCodes P cs
end

/-- A table's row's code: a type cell as its key's test, a step cell as its result, every cell as its values. -/
def rowCode (P : Prog) (r : List (Option CellBody)) : RowCode :=
  { key := match cellAt r 0 with
      | some (.ty (.ty t)) => some (linT ⟨P, #[]⟩ t)
      | _ => none
    res := match cellAt r 1 with
      | some (.stmt s) => some (linS ⟨P, #[]⟩ [] s)
      | _ => none
    cells := r.map fun c => c.map (cellCode P) }

/-- An owner's closures and steps: an algorithm's, else an SDO row's. -/
def ownerOf (P : Prog) (a : AlgId) : Option (Array CloLit × List Stmt) :=
  match P.alg a with
  | some g => some (g.closures, g.body)
  | none => (P.rowOf a).map fun r => (r.closures, r.body)

/-- The code of each closure literal of the algorithm or SDO row `a`, numbered under the step that makes it
(`cloUnits` over `a`'s own code). -/
def ownerClos (P : Prog) (a : AlgId) : Array (Option (List Nat × Code)) :=
  match ownerOf P a with
  | some (cls, body) => cloUnits P cls (linNodes ⟨P, cls⟩ body 1 [])
  | none => #[]

/-- The machine's program of `P`: each unit's steps from 1 under the empty path, a closure's under its literal's step. -/
def Prog'.of (P : Prog) : Prog' where
  P := P
  alg a := (P.alg a).map fun g => linNodes ⟨P, g.closures⟩ g.body 1 []
  row s k := (P.row s k).map fun r => linNodes ⟨P, r.closures⟩ r.body 1 []
  clo site := ((ownerClos P site.alg)[site.idx]?).join
  tstep t := (P.table t).map fun tb => tb.grid.tail.map (rowCode P)
  earlyRow p i := ((P.early p)[i]?).map (linRow P)
  earlyOwn ps := linOwn P ps
  earlyTree p := linTree P p
  covered p := linCovered P p
  clauseRows c := (P.clauseTables c).map fun tb => tb.grid.tail.map (rowCode P)

end Ecma.Machine
