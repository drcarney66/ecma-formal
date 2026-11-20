module

public import Ecma.Lower.LinExpr
public import Ecma.Notation.Early

@[expose] public section

/-!
# Early errors as code (§5.3)

An early-error rule row at a Parse Node gives one new *SyntaxError* object per sentence whose condition holds;
the errors of a row are a tuple (`Val.tuple`) until the SDO Early Errors makes a List of them.

- `linRow`: a rule row. Its sentences add to the tuple in the slot after its variables; a row whose tuple is
  empty, or with a `This rule is not applied if …` sentence that holds, gives none.
- `linOwn`: the rules of some productions at a node, their rows in order: the must-cover rules first, and the
  others only if those give no error (a cover that fails is the node's early error, and the other rules read
  through the cover; overlay clause formal-early-errors-cover-rules-first).
- `linTree`: a node and its descendants. Each child node no rule says must cover a nonterminal (`linCovered`:
  §5.1.5, no rules apply to a covered child or its descendants), then the node's own rules, if the children
  gave none.
-/

namespace Ecma.Machine
open Ecma

/-- The tuple of no values. -/
def tupNil : Op := .leaf .tuple []

/-- Slot `acc`'s tuple with the tuple `e` after it. -/
def tupAdd (acc : Slot) (e : Op) : Ins := .let_ acc (.leaf .tupCat [.var acc, e])

mutual
/-- Whether a sentence says a child must cover a nonterminal, under any condition or reading. -/
def _root_.Ecma.EarlySentence.hasCover : EarlySentence → Bool
  | .mustCover .. => true
  | .ifInline _ s => s.hasCover
  | .layout _ ss => EarlySentence.hasCoverAll ss
  | .readings _ lit alts => EarlySentence.hasCoverAll lit || EarlySentence.hasCoverAlts alts
  | _ => false

def _root_.Ecma.EarlySentence.hasCoverAll : List EarlySentence → Bool
  | [] => false
  | s :: ss => s.hasCover || EarlySentence.hasCoverAll ss

def _root_.Ecma.EarlySentence.hasCoverAlts : List (Reading × List EarlySentence) → Bool
  | [] => false
  | (_, ss) :: rest => EarlySentence.hasCoverAll ss || EarlySentence.hasCoverAlts rest
end

/-- Whether row `r` is a must-cover rule. -/
def _root_.Ecma.EarlyRow.hasCover (r : EarlyRow) : Bool := EarlySentence.hasCoverAll r.body

section
variable (cx : Cx) (acc : Slot) (err browser : Op)

mutual
/-- A sentence: the errors it gives, added to slot `acc`'s tuple. `err` makes a new *SyntaxError*; `browser` is
whether the host supports B.1.2, whose `<ins>` conditions apply then. -/
def linSent : EarlySentence → Code
  | .syntaxError _ c none => [.br (linC cx c) [tupAdd acc (.leaf .tuple [err])] []]
  | .syntaxError _ c (some (_, d)) => [.br (linC cx c) [.br (linC cx d) [] [tupAdd acc (.leaf .tuple [err])]] []]
  | .syntaxErrorIns c d =>
    [.br (linC cx c) [.br browser [.br (linC cx d) [tupAdd acc (.leaf .tuple [err])] []]
      [tupAdd acc (.leaf .tuple [err])]] []]
  | .mustCover p (.nt _ k _) => [.cover acc (linE cx p) k err]
  | .mustCover p _ => [.eval (linE cx p), .stop .sortError]
  | .rulesApplied ps _ => [tupAdd acc (.call (.earlyOwn ps) [])]
  | .ifInline c s => [.br (linC cx c) (linSent s) []]
  | .forEachIn x t l c _ =>
    [.loop (some x) (.each (linE cx l) false) []
      [.br (.bind (.var x) (linT cx t)) [.br (linC cx c) [tupAdd acc (.leaf .tuple [err])] []] []]]
  | .info _ | .notApplied _ _ => []
  | .layout _ ss => linSents ss
  | .readings e lit alts => Ins.ofSentReadings e (linSents lit) (linSentAlts alts)
  | .stmt _ => [.stop .residue]

def linSents : List EarlySentence → Code
  | [] => []
  | s :: ss => linSent s ++ linSents ss

def linSentAlts : List (Reading × List EarlySentence) → List (Reading × Code)
  | [] => []
  | (q, ss) :: rest => (q, linSents ss) :: linSentAlts rest
end
end

section
variable (cx : Cx)

mutual
/-- The conditions of a row's `This rule is not applied if …` sentences, in order. -/
def notApplied : List EarlySentence → List Op
  | [] => []
  | .notApplied c _ :: ss => linC cx c :: notApplied ss
  | .layout _ ls :: ss => notApplied ls ++ notApplied ss
  | .readings e lit alts :: ss => Op.ofReadings e (.or (notApplied lit)) (notAppliedAlts alts) :: notApplied ss
  | _ :: ss => notApplied ss

def notAppliedAlts : List (Reading × List EarlySentence) → List (Reading × Op)
  | [] => []
  | (q, ss) :: rest => (q, .or (notApplied ss)) :: notAppliedAlts rest
end

mutual
/-- Whether a sentence says the bound subject, a child of the node, must cover a nonterminal; none: it says so
of no child, and evaluates nothing. -/
def covSent : EarlySentence → Option Op
  | .mustCover p _ => some (.leaf .sameNode [linE cx p, .bound])
  | .ifInline k s => some (.and [linC cx k, (covSent s).getD (.const (.val .false))])
  | .layout _ ss => match covSents ss with
    | [] => none
    | os => some (.or os)
  | .readings e lit alts => some (Op.ofReadings e (.or (covSents lit)) (covAlts alts))
  | _ => none

def covSents : List EarlySentence → List Op
  | [] => []
  | s :: ss => match covSent s with
    | some o => o :: covSents ss
    | none => covSents ss

def covAlts : List (Reading × List EarlySentence) → List (Reading × Op)
  | [] => []
  | (q, ss) :: rest => (q, .or (covSents ss)) :: covAlts rest
end
end

/-- A new *SyntaxError* object. -/
def newSyntaxError (P : Prog) : Op := .call (.phrase Known.phNewError) [.const (.fieldName P.syntaxError)]

/-- Whether the host supports B.1.2 (regular expression patterns). -/
def supportsRegExpPatterns (P : Prog) : Op :=
  match P.overlayClause .regExpPatterns with
  | some c => .leaf .toBool [.call (.prim Known.pWebBrowser) [.const (.data (.choice 0)), .const (.clause c)]]
  | none => .const (.val .false)

/-- A rule row's early errors at the frame's Parse Node, and the slots its frame has: its variables, then the
tuple. -/
def linRow (P : Prog) (r : EarlyRow) : Nat × Code :=
  let acc := r.vars.size
  let cx : Cx := ⟨P, #[]⟩
  (acc + 1,
    [.let_ acc tupNil] ++ linSents cx acc (newSyntaxError P) (supportsRegExpPatterns P) r.body ++
    [.br (.leaf .tupEmpty [.var acc]) [.ret tupNil] [],
     .br (.or (notApplied cx r.body)) [.ret tupNil] [],
     .ret (.var acc)])

/-- The rows of the productions `ps`, each with its production and position among its rows. -/
def earlyRowsOf (P : Prog) (ps : List ProdId) : List (ProdId × Nat × EarlyRow) :=
  ps.flatMap fun p => (P.early p).zipIdx.map fun (r, i) => (p, i, r)

/-- The rows' errors, in order, added to slot 0's tuple. -/
def addRows (rows : List (ProdId × Nat × EarlyRow)) : Code :=
  rows.map fun (p, i, _) => tupAdd 0 (.call (.earlyRow p i) [])

/-- The early errors of the rules of the productions `ps` at the frame's Parse Node (slot 0: the tuple): the rules that
say a child must cover a nonterminal first, the others only if those report none (overlay clause
formal-early-errors-cover-rules-first). -/
def linOwn (P : Prog) (ps : List ProdId) : Code :=
  let rows := earlyRowsOf P ps
  [.let_ 0 tupNil] ++ addRows (rows.filter (·.2.2.hasCover)) ++
    [.br (.leaf .tupEmpty [.var 0]) (addRows (rows.filter (!·.2.2.hasCover))) [],
     .ret (.var 0)]

/-- Whether a rule of production `p` says the bound subject, a child, must cover a nonterminal. -/
def linCovered (P : Prog) (p : ProdId) : Op :=
  .or ((P.early p).flatMap fun r => covSents ⟨P, #[]⟩ r.body)

/-- The early errors of a node of production `p` and of its descendants (slot 0: the children's tuple; slot 1:
a child): the node's own rules only when its descendants have none (EarlyErrorsOf, overlay clause
formal-earlyerrorsof). -/
def linTree (p : ProdId) : Code :=
  [.let_ 0 tupNil,
   .loop (some 1) (.kids none) []
     [.br (.leaf .isNode [.var 1])
       [.br (.call .covered [.var 1]) [] [tupAdd 0 (.on .earlyTree (.var 1) [])]] []],
   .br (.leaf .tupEmpty [.var 0])
     [.ret (.call (.earlyOwn [p]) [])]
     [.ret (.var 0)]]

end Ecma.Machine
