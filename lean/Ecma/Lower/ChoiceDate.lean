module

public import Ecma.Ops.ProgPrim

@[expose] public section

/-!
# The date algorithms' choices made constructive

`Prog.expandChoiceDate`: YearFromTime's "the largest integral y such that TimeFromYear(y) ≤ tv"
(§21.4.1.7) becomes YearFromTimeOf(tv) (`Known.pYearFromTimeOf`), and MakeDay's literal "Find a
finite time value t such that …" (§21.4.1.28 step 8) becomes FirstDayOf(ℝ(balancedYear),
balancedMonthMV) (`Known.pFirstDayOf`), its not-found steps where that is NaN. Each step is matched
as written, in its algorithm's top-level steps; MakeDay's readings and their alternative are kept.
-/

namespace Ecma

/-- `P` with each algorithm's steps given by `B` at its id; its id, header, variables and closures kept. -/
def Prog.mapBodies (P : Prog) (B : AlgId → Alg → List Node) : Prog :=
  { P with alg := fun a => (P.alg a).map fun g => { g with body := B g.id g } }

namespace Choice.Date

def yftId : AlgId := ⟨1321, 0⟩

def makeDayId : AlgId := ⟨1342, 0⟩

/-- YearFromTime's step as YearFromTimeOf(tv); `none` for any other step. -/
def yftSite : Stmt → Option Stmt
  | .ret (some (.extreme true 1 (.sort _ [] 9 _) (.rel .le (.call (.alg ⟨1320, 0⟩) [.var 1]) (.var 0)))) =>
    some (.ret (some (.call (.prim Known.pYearFromTimeOf) [.var 0])))
  | _ => none

/-- FirstDayOf(ℝ(balancedYear), balancedMonthMV). -/
def firstDayE : Expr := .call (.prim Known.pFirstDayOf) [.call (.prim Known.pR) [.var 6], .var 7]

/-- MakeDay's literal find as FirstDayOf, its not-found steps where that is NaN; `none` for any other step. -/
def makeDaySite : Stmt → Option Stmt
  | .readings 107 (.findSuchThat 8 (.sort _ [121] 122 _) (.and .comma
      [.rel .eq (.call (.alg ⟨1321, 0⟩) [.var 8]) (.call (.prim 1) [.var 6]),
       .rel .eq (.call (.alg ⟨1324, 0⟩) [.var 8]) (.var 7),
       .rel .eq (.call (.alg ⟨1325, 0⟩) [.var 8]) (.math .none (.num (.dec 1)))]) _ f) alts =>
    some (.readings 107 (.ifElse (.preds firstDayE (.isVal false .or [.val (.nan .none)]) []) f (.let_ 8 firstDayE))
      alts)
  | _ => none

/-- The site rewrite of algorithm `a`. -/
def site (a : AlgId) : Stmt → Option Stmt :=
  if a == yftId then yftSite else if a == makeDayId then makeDaySite else fun _ => none

/-- A step, rewritten where it is a site. -/
def step (a : AlgId) : Node → Node
  | .mk atts s => .mk atts ((site a s).getD s)

/-- Algorithm `a`'s steps with its sites rewritten. -/
def body (a : AlgId) (g : Alg) : List Node := g.body.map (step a)

end Choice.Date

/-- `P` with the date algorithms' choice sites rewritten (`Choice.Date.site`). -/
def Prog.expandChoiceDate (P : Prog) : Prog := P.mapBodies Choice.Date.body

end Ecma
