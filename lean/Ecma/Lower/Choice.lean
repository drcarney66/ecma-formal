module

public import Ecma.Lower.ChoiceDate

@[expose] public section

/-!
# The choices made constructive

`Prog.expandChoice`: the date algorithms' choices (`Prog.expandChoiceDate`), with the build-time check that each
is found (`Prog.choiceSitesUnmatched`).
-/

namespace Ecma

namespace Choice

/-- The algorithms whose steps hold a choice site that a constructive function makes, each with how many: YearFromTime's
step and MakeDay's step 8 (`Date.site`, among the top-level steps). -/
def sites : List (AlgId × Nat) := [(Date.yftId, 1), (Date.makeDayId, 1)]

/-- The choice sites algorithm `a`'s steps `g` hold, as `Prog.expandChoice` finds them. -/
def sitesIn (a : AlgId) (g : Alg) : Nat :=
  (g.body.filter fun | .mk _ s => (Date.site a s).isSome).length

end Choice

/-- The algorithms of `Choice.sites` whose steps in `P` do not hold their choice sites: a site is matched by its
algorithm's id and by the shape of its steps, so where a change of the text moves a step out of that shape the step
keeps the text's choice, which the machine cannot make. -/
def Prog.choiceSitesUnmatched (P : Prog) : List AlgId :=
  Choice.sites.filterMap fun (a, n) => match P.alg a with
    | some g => if Choice.sitesIn a g == n then none else some a
    | none => some a

/-- `P` with every choice site the constructive functions make replaced. -/
def Prog.expandChoice (P : Prog) : Prog := P.expandChoiceDate

end Ecma
