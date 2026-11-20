module

public import Engine.Host.Core

@[expose] public section

/-!
# The job loop's stop

The site of a stop the job loop makes (`jobSite`), as ecma-run prints it.
-/

namespace Engine.Host

open Ecma Engine

/-- The site of the job loop's stop `r`, the erratum of a Job's clause (`errata`, as `Names.jobErrata`):
`sec-jobs -`, the clause making that erratum's Jobs (named by `name`) its caller where it is the only one. -/
def jobSite (name : ClauseId → String) (errata : List (ClauseId × ErratumId)) (r : Res Impl (Val Impl)) :
    String × List String :=
  match r with
  | .stop (.erratum e) =>
    match errata.filter (·.2 == e) with
    | [] => ("? ?", [])
    | [(c, _)] => ("sec-jobs -", [name c])
    | _ => ("sec-jobs -", [])
  | _ => ("? ?", [])

end Engine.Host
