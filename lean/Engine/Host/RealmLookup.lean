module

public import Ecma.Gen.Decls
public import Ecma.Gen.Index
public import Std.Data.HashMap
public import Ecma.Spec.Program

@[expose] public section

/-!
# The starting realm of a whole program

`specRealmBy D` leaves one execution context with a Realm on the stack: InitializeHostDefinedRealm
by `call`, which runs an algorithm.
-/

namespace Engine.Host.RealmLookup

open Ecma Ecma.Spec

def readingOf (e : ErratumId) : Reading := (Ecma.Gen.parity[e]?).getD .literal

def algNamed? (n : String) : Option Alg := allAlgs.find? (·.name == n)

end Engine.Host.RealmLookup
