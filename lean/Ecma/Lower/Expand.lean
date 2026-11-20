module

public import Ecma.Lower.Plan
public import Ecma.Lower.Calls
public import Ecma.Notation.Early
public import Ecma.Notation.Tables
public import Ecma.Notation.Realm
public import Ecma.Lower.Src
public import Ecma.Lower.Choice
public import Ecma.Lower.Such

@[expose] public section

/-!
# The expanded program

`Spec.Plan.expandProg pl Q`: `Q` with the plan's code sites specialized (`Tables.rewrite`), then its
phrases as calls (`Prog.calls`), then its binding conditions as a call and a branch (`Prog.expandSuch`,
over the specialized holes). Specialization comes first: a type phrase's predicate form (`TyExpr.pred`),
which the calls give, is outside the fragments a specialized site's premises read. `Src.expanded s extras`:
the source's program with its choices made constructive (`Prog.expandChoice`; before the calls, so that
its leaves' prose become calls too), its plan's declarations (computed from the source's own
program), and the algorithms `extras` where the source defines none, so expanded.
-/

namespace Ecma

/-- `Q` with the plan's code sites specialized, then its phrases as calls, then its binding conditions. -/
def Spec.Plan.expandProg (pl : Spec.Plan) (Q : Prog) : Prog := Prog.expandSuch (Prog.calls (pl.tables.rewrite Q))

/-- The program of `s`, with the algorithms `extras` where `s` defines none (where `s` defines one, `s`'s),
expanded: its choices made constructive, its plan's declarations added, then the plan's expansion
(`Spec.Plan.expandProg`). -/
def Src.expanded (s : Src) (extras : AlgId → Option Alg) : Prog :=
  let pl := Spec.Plan.ofSrc s
  let Q := (pl.decl s.prog s.expandMacros.rows).declare s.prog.expandChoice
  pl.expandProg { Q with alg := fun a => (Q.alg a).or (extras a) }

end Ecma
