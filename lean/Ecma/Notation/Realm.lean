module

public import Ecma.Notation.Repr

@[expose] public section

/-!
# Ecma realm table: the data shape

The built-in objects that clauses 19-28, Annex B.2, %ThrowTypeError% and
%ForInIteratorPrototype% specify, read under §18's conventions: each object's
intrinsic names, kind, [[Prototype]], internal slots, CreateBuiltinFunction's
arguments for a function, and its properties with their values and attributes;
and the global object's properties. Objects are listed in a creation order: each
after its [[Prototype]]. An object is referred to by its index in that list.
-/

namespace Ecma

/-- A property key: a String, or a well-known symbol by its description (`Symbol.iterator`). -/
inductive RKey where
  | str (s : String)
  | sym (description : String)
  deriving Repr, BEq, Inhabited

/-- A value of the table. -/
inductive RVal where
  | undefined
  | null
  | bool (b : Bool)
  | str (s : String)
  /-- a Number, by its IEEE 754 binary64 bits -/
  | number (bits : UInt64)
  /-- an object of the table, by index -/
  | obj (i : Nat)
  /-- a well-known symbol, by its description (`Symbol.iterator`) -/
  | sym (description : String)
  /-- _realm_.[[GlobalEnv]].[[GlobalThisValue]] of the realm being created -/
  | globalThis
  /-- the object the algorithm creates when the realm is created -/
  | created (alg : AlgId)
  deriving Repr, BEq, Inhabited

/-- A property's attributes ([[Writable]] is false for an accessor). -/
structure RAttrs where
  writable : Bool
  enumerable : Bool
  configurable : Bool
  deriving Repr, BEq, Inhabited

/-- A property's value: data, or an accessor's halves (none: *undefined*). -/
inductive RPVal where
  | data (v : RVal)
  | accessor (get set : Option Nat)
  deriving Repr, BEq, Inhabited

/-- A property of a built-in object, with the clause that specifies it; `annexB`: B.2's;
`optional`: a `normative-optional` clause's (both required when the host is a web browser, else a
host choice); `omittable`: one a host may omit (§25.2.2: SharedArrayBuffer). -/
structure RProp where
  key : RKey
  val : RPVal
  attrs : RAttrs
  clause : ClauseId
  annexB : Bool
  optional : Bool
  omittable : Bool
  deriving Repr, BEq, Inhabited

/-- CreateBuiltinFunction's arguments, and the attributes of "length" and "name". -/
structure RFun where
  /-- none: a behaviour given in prose -/
  alg : Option AlgId
  length : Nat
  name : RKey
  pfx : Option String
  ctor : Bool
  /-- described as async -/
  async : Bool
  lengthAttrs : RAttrs
  nameAttrs : RAttrs
  deriving Repr, BEq, Inhabited

/-- An object's kind: ordinary, or exotic by the clause that defines its kind. -/
inductive RKind where
  | ordinary
  | exotic (c : ClauseId)
  deriving Repr, BEq, Inhabited

/-- A built-in object. -/
structure RObj where
  /-- its intrinsic names (`Array.prototype` for `%Array.prototype%`) -/
  names : List IntrinsicId
  /-- the same names as [[Intrinsics]] field names (`%Array.prototype%`) -/
  keys : List FieldId
  /-- its access path as the spec writes it (`Array.prototype.push`, `get Map.prototype.size`) -/
  path : String
  clause : ClauseId
  kind : RKind
  /-- none: *null* -/
  proto : Option Nat
  extensible : Bool
  slots : List (FieldId × RVal)
  fn? : Option RFun
  /-- its properties in clause order: the key list a host's property order permutes -/
  props : List RProp
  annexB : Bool
  optional : Bool
  deriving Repr, BEq, Inhabited

/-- The realm table a program carries: the objects in creation order, the properties of the
clauses that specify no intrinsic's, the well-known symbols' descriptions, and the field names. -/
structure RealmTable where
  objs : List RObj := []
  clauseProps : List (ClauseId × List RProp) := []
  symbols : List String := []
  fieldName : FieldId → String := fun _ => ""

end Ecma
