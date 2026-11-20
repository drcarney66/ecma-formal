module

public import Ecma.State

@[expose] public section

/-!
# Erratum stops

A stop `.erratum e` names its erratum; the `stops=` rows of readings.emu cross-check it by the
stop's site and callers: the labelling of ecma-run's result line
(`stop: erratum <Name> <site>`, ` (unregistered site)` after it where no row has the site).
-/

namespace Engine.Cli

open Ecma

/-- Whether a row `(e, clause id, step path, innermost caller's clause id)` of `stops` registers
erratum `k` at the site `site` (`sec-id#idx path`) under the callers `cs` (innermost first); a site
with step `?` (a blame that names neither step nor callers) by any row of its clause. -/
def registeredAt {α : Type} [BEq α] (stops : Array (α × String × String × Option String)) (k : α)
    (site : String) (cs : List String) : Bool :=
  match site.splitOn " " with
  | [at_, path] =>
    let cl := (at_.splitOn "#").headD at_
    stops.any fun (e, c, p, kc) =>
      e == k && c == cl && (path == "?" || p == path && kc.all (cs.head? == some ·))
  | _ => false

/-- The text of the stop `r` if it is erratum `e`'s: `name e`, marked where `stops` does not register
`key e` at the site. -/
def erratumText {α : Type} [BEq α] (stops : Array (α × String × String × Option String))
    (key : ErratumId → α) (name : ErratumId → String) (r : Stop) (site : String) (cs : List String) :
    Option String :=
  match r with
  | .erratum e => some (if registeredAt stops (key e) site cs then name e else s!"{name e} (unregistered site)")
  | _ => none

/-- The erratum and reading `--erratum NAME=READING` names (`literal`, `test262` or `proposed`). -/
def erratumReading (arg : String) : Option (String × Reading) :=
  match arg.splitOn "=" with
  | [n, "literal"] => some (n, .literal)
  | [n, "test262"] => some (n, .test262)
  | [n, "proposed"] => some (n, .proposed)
  | _ => none

/-- `rd` with the readings `rs` of the errata they name (`names`, by id) over it, the last for a name. -/
def readingsOver (names : Array String) (rs : List (String × Reading)) (rd : ErratumId → Reading) :
    ErratumId → Reading :=
  fun e => ((rs.reverse.find? fun (n, _) => names[e]? == some n).map (·.2)).getD (rd e)

end Engine.Cli
