module

public import Ecma.State
public import Engine.Model

@[expose] public section

/-!
# The names a host and a program driver look up

The Bare host (`Engine.Host.Core`, `Engine.Host.Opts`) and the program driver (`Engine.Host.Program`) know
the clauses, fields, enums and sorts only through a `Names`, so that they need neither Ecma.Gen nor
the machine: `Engine.SpecHost.names` builds Ecma.Gen's.
-/

namespace Engine.Host

open Ecma

/-- The name lookups of a host and a program driver. -/
structure Names where
  /-- A clause's sec-id. -/
  clause : ClauseId → Option String
  /-- A clause by its sec-id. -/
  clauseOf? : String → Option ClauseId
  /-- A field by its name (the first of that name). -/
  field? : String → Option FieldId
  /-- The fields of that name. -/
  fieldsNamed : String → List FieldId
  /-- An enum by its name. -/
  enum? : String → Option EnumId
  /-- An enum's name. -/
  enumName : EnumId → Option String
  /-- A sort by its name. -/
  sort? : String → Option SortId
  /-- A sort's direct supersorts. -/
  sortSuper : SortId → List SortId
  /-- The clauses whose Jobs check for an abrupt completion at the job loop. -/
  checkedJobs : List ClauseId := []

namespace Names

variable (N : Names)

/-- A clause's sec-id, or `clause c` where it has none. -/
def clauseName (c : ClauseId) : String := (N.clause c).getD s!"clause {c}"

/-- A logged call is one of the host-defined operation with that sec-id. -/
def callOf {M : Model} (sec : String) : HostCall M → Bool
  | .hook c _ _ _ _ => N.clause c == some sec
  | _ => false

/-- `k` is the sort `t` or a subsort of it, by `sortSuper` (to depth `f`). -/
def subSort : Nat → SortId → SortId → Bool
  | 0, k, t => k == t
  | f + 1, k, t => k == t || (N.sortSuper k).any (subSort f · t)

/-- A value is a Record of the sort named `sort`, or of a subsort of it. -/
def isRecordOf {M : Model} (s : State M) (sort : String) : Val M → Bool
  | .ref a => match M.heapGet s.heap a, N.sort? sort with
    | some (.record k _), some t => N.subSort 64 k t
    | _, _ => false
  | _ => false

end Names

/-- How the engine's drivers run the program: an algorithm's call and an Abstract Closure's, each to its end,
and what the leaf operations read. -/
structure Runner where
  call : AlgId → List (Val Engine.Impl) → Run Engine.Impl (Val Engine.Impl)
  clo : CloSite → List (Val Engine.Impl) → List (Val Engine.Impl) → Run Engine.Impl (Val Engine.Impl)
  /-- the host's Jobs (§9.5), until it has none or one completes abruptly; ClearKeptObjects by its algorithm -/
  jobs : Option AlgId → Run Engine.Impl (Val Engine.Impl)
  leaf : LeafCtx Engine.Impl

end Engine.Host
