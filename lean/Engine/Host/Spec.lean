module

public import Ecma.Host.Laws
public import Ecma.Notation.AlgKey
public import Ecma.Prims.Numbers
public import Ecma.Gen.Decls
public import Engine.Host.Core

@[expose] public section

/-!
# The host of a whole program, at Impl, over Ecma.Gen

The Bare host (`Engine.Host.host`) at Ecma.Gen's names (`names`): the host-defined operations
the specification calls (by sec-id, resolved through `Ecma.Gen.clauses`), its choices at the host
primitives, its jobs (the queue is the host-call log), `print`, a host-defined built-in function
whose lines go to a host-owned List, `$262`'s detachArrayBuffer, createRealm, evalScript and IsHTMLDDA, and HostLoadImportedModule's
host algorithm; and the host's algorithms by id (`hostAlgs`), beside the specification's in the program.
-/

/-- A clause's sec-id; irreducible, so that no reduction unfolds the clause table. -/
@[irreducible] def Ecma.secOf (c : Ecma.ClauseId) : Option String := Ecma.Gen.clauses[c]?

namespace Engine.SpecHost

open Ecma Engine

/-- Ecma.Gen's names. -/
def names : Engine.Host.Names where
  clause := secOf
  clauseOf? sec := Ecma.Gen.clauses.idxOf? sec
  field? n := Ecma.Gen.fields.idxOf? n
  fieldsNamed n := (List.range Gen.fields.size).filter (Gen.fields[·]? == some n)
  enum? n := Ecma.Gen.enums.idxOf? n
  enumName e := Ecma.Gen.enums[e]?
  sort? n := Ecma.Gen.sorts.idxOf? n
  sortSuper k := ((Gen.sortDefs[k]?).join.map (·.super)).getD []
  jobErrata := Gen.jobErrata.toList

export Engine.Host (Cells elems readList writeElems setRealm unused normal Hook printClause printAlg
  clearKeptSec printLine loadedClause storeClause sourceClause keyClause empty loadedIn keyIn referrerKey loadedModule moduleLoaded
  moduleSource moduleKey
  ownHook detachAlg createRealmAlg evalScriptAlg isHTMLDDAAlg isHTMLDDABuiltin
  nanEncoding pairChoice choice genericJob promiseJob timeoutJob cleanupJob clearsKept abrupt)

/-- A clause's sec-id. -/
abbrev clauseName (c : ClauseId) : String := names.clauseName c

/-! The Bare host at Ecma.Gen's names. -/

abbrev printBuiltin := Engine.Host.printBuiltin names
abbrev detachBuiltin := Engine.Host.detachBuiltin names
abbrev createRealmBuiltin := Engine.Host.createRealmBuiltin names
abbrev evalScriptBuiltin := Engine.Host.evalScriptBuiltin names
abbrev loaderAlg := Engine.Host.loaderAlg names
abbrev loaderBuiltin := Engine.Host.loaderBuiltin names

/-- The agent API's algorithms (`Engine.Host.agentBuiltins`), built once. -/
def agentAlgs : Array Alg := (Engine.Host.agentBuiltins names).toArray

/-- The agent API's algorithm of that id: one of `startAlg` to `setTimeoutAlg`, looked up in `agentAlgs`. -/
def agentAlg (a : AlgId) : Option Alg :=
  if a.idx == 0 && Engine.Host.startAlg.clause ≤ a.clause && a.clause ≤ Engine.Host.setTimeoutAlg.clause then
    agentAlgs.find? (·.id == a)
  else none

/-- The algorithms that run a program (`Engine.Host.firstBuiltins`), built once. -/
def firstAlgs : Array Alg := (Engine.Host.firstBuiltins names).toArray

/-- The host's built-in function, agent API algorithm, HostLoadImportedModule or algorithm that runs a program at
`k`. -/
def hostAt (k : AlgId) : Option Alg :=
  if k == printAlg then some printBuiltin else if k == detachAlg then some detachBuiltin
  else if k == createRealmAlg then some createRealmBuiltin else if k == evalScriptAlg then some evalScriptBuiltin
  else if k == isHTMLDDAAlg then some isHTMLDDABuiltin
  else if k == loaderAlg then some loaderBuiltin
  else if let some g := agentAlg k then some g
  else if k.idx == 0 && Engine.Host.runScriptAlg.clause ≤ k.clause && k.clause ≤ Engine.Host.parseModuleAlg.clause then
    firstAlgs.find? (·.id == k)
  else none

/-- The host's algorithms by id, as the program's indexes find an algorithm (`Src.algKey`): its built-in
functions, the agent API's algorithms, HostLoadImportedModule and the algorithms that run a program. -/
def hostAlgs (a : AlgId) : Option Alg := hostAt (Src.keyId a)

end Engine.SpecHost
