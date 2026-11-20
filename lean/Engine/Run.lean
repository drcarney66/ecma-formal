module

public import Engine.Host.SpecOpts
public import Engine.Host.Program
public import Engine.Host.RealmLookup

@[expose] public section

/-!
# A whole program at Impl, over Ecma.Gen

The starting realm and the host's cells (`setup`), then the Bare
program (`runFrom`, `run`): the driver `Engine.Host.setup`/`runFrom` at Ecma.Gen's names and
realm; its outcome (`outcome`).
-/

namespace Engine.SpecRun

open Ecma Engine Engine.SpecHost Engine.Host.RealmLookup

abbrev F := Engine.Impl

/-! The Bare program at Ecma.Gen's names. -/

export Engine.Host (str component takeRealm JobPolicy Source hex4 escapeUnit escapeUnits
  displayUnits display objectCell dataProperty showNum bigText addrNat stopName s0 setupFailed)

abbrev outcome := Engine.Host.outcome names

/-- InitializeHostDefinedRealm, Ecma.Gen's. -/
def realmAlg : Option AlgId := (algNamed? "InitializeHostDefinedRealm").map (·.id)

/-- The well-known symbols, Ecma.Gen's. -/
def realmSyms : Nat := Ecma.Gen.Realm.symbols.length

/-- The realm by InitializeHostDefinedRealm through `mk` (`print` and `$262` its host-defined global
properties), set up for the host with the options `ho`: the host's cells (`Engine.Host.setup`). -/
abbrev setup := Engine.Host.setup names realmAlg realmSyms

/-- `src` (as `sr` has it) from a set-up state `s` (`setup`) by the dispatcher `mk`, the host's options `ho`
(`Engine.Host.runFrom`). -/
abbrev runFrom := @Engine.Host.runFrom names

end Engine.SpecRun
