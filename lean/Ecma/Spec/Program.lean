module

public import Ecma.Gen.Tables
public import Ecma.Gen.Index
public import Ecma.Gen.Early
public import Ecma.Gen.Decls
public import Ecma.Gen.Realm
public import Ecma.Grammar.Derives
public import Ecma.Lower.Src
public import Ecma.Grammar.Gen.Index
public import Std.Data.HashMap

@[expose] public section

/-!
# The specification's program

`prog` is the whole program as data: every algorithm and SDO row by `AlgId`,
GL's chain productions, the concrete methods by Record sort, the phrase
meanings.
-/

namespace Ecma.Spec

open Ecma

def allAlgs : List Alg := Ecma.Gen.algs.flatten

/-- Every SDO row: the clauses', then the overlay's phrase rows (`Ecma.Gen.rows` ends with them). -/
def allRows : List SdoRow := Ecma.Gen.rows.flatten

/-- GL as `Grammar.Derives` reads it, with §12.10's class of each `;`. -/
def gl : Grammar.GL :=
  ⟨Grammar.Gen.grammars, Grammar.Gen.prodIds, Grammar.Gen.prodNext, Grammar.Gen.blocks,
    Grammar.Gen.semis.map fun s => (s.prod.ctorIdx, s.pos, s.semi)⟩

/-- The realm table of `Ecma.Gen.Realm`. -/
def realmTable : RealmTable :=
  { objs := Ecma.Gen.Realm.objs, clauseProps := Ecma.Gen.Realm.clauseProps,
    symbols := Ecma.Gen.Realm.symbols, fieldName := fun f => Ecma.Gen.fields[f]?.getD "" }

/-- The data's source arrays. -/
def src : Src where
  algs := allAlgs
  rows := allRows
  decls := Ecma.Gen.decls
  earlyRows := Ecma.Gen.earlyRows.flatten
  tables := Ecma.Gen.tables.flatten
  gl := gl
  realm := realmTable

end Ecma.Spec
