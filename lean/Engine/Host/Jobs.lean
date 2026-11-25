module

public import Engine.Host.Core

@[expose] public section

/-!
# The job loop's stop

The site of a stop the job loop makes (`jobSite`), as ecma-run prints it.
-/

namespace Engine.Host

open Ecma Engine

/-- The site of the job loop's stop `r`: `sec-jobs -`, the clause whose Jobs check for an abrupt completion
(named by `name`) its caller where it is the only one. -/
def jobSite (name : ClauseId → String) (checkedJobs : List ClauseId) (r : Res Impl (Val Impl)) :
    String × List String :=
  match r with
  | .stop .assertFailed =>
    match checkedJobs with
    | [] => ("? ?", [])
    | [c] => ("sec-jobs -", [name c])
    | _ => ("sec-jobs -", [])
  | _ => ("? ?", [])

end Engine.Host
