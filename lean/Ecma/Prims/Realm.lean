module

public import Ecma.State
public import Ecma.Notation.Realm

@[expose] public section

/-!
# Realm primitives: the realm table as Records

The primitives IntrinsicObjects, ClauseProperties, RealmIntrinsic, SetFieldNamed, IsIntrinsicName and
WellKnownSymbol over the program's realm table (`RealmTable`), as `spec/formal/realm.emu` declares them: each
object and each property a new Record; a well-known symbol `i` is `M.symNew i` with its description.
-/

namespace Ecma.Prims.Realm

variable {M : Model}

/-- A new Record of the fields. -/
def newRec (fs : List (FieldId × Val M)) : Run M (Val M) := do
  return .ref (← alloc (.record Known.sRecord (fs.foldl (fun r (f, v) => M.recSet r f v) M.recEmpty)))

/-- ~empty~. -/
def empty : Val M := .enum Known.eEmpty

/-- §6.1.6.1: the Number whose IEEE 754 binary64 encoding is `b`. -/
def numOfBits (b : UInt64) : M.Num :=
  let n := b.toNat
  let neg := n / 2 ^ 63 == 1
  let e := n / 2 ^ 52 % 2 ^ 11
  let m := n % 2 ^ 52
  let two (k : Nat) : M.Math := M.pow (M.ofNat 2) (M.ofNat k)
  if e == 2 ^ 11 - 1 then (if m == 0 then M.numInf neg else M.numNaN)
  else if e == 0 && m == 0 then M.numZero neg
  else
    let mag := if e == 0 then M.div (M.ofNat m) (two 1074)
      else if e ≥ 1075 then M.mul (M.ofNat (2 ^ 52 + m)) (two (e - 1075))
      else M.div (M.ofNat (2 ^ 52 + m)) (two (1075 - e))
    M.numOf (if neg then M.neg mag else mag)

/-- The well-known symbol with the description `d`. -/
def symOf (T : RealmTable) (d : String) : Option (Val M) :=
  (T.symbols.idxOf? d).map fun i => .sym (M.symNew i (some (M.strLit d)))

/-- A property key. -/
def keyVal (T : RealmTable) : RKey → Option (Val M)
  | .str s => some (.str (M.strLit s))
  | .sym d => symOf T d

/-- A value that is no object of the table. -/
def plainVal (T : RealmTable) : RVal → Option (Val M)
  | .undefined => some .undefined
  | .null => some .null
  | .bool b => some (.bool b)
  | .str s => some (.str (M.strLit s))
  | .number b => some (.num (numOfBits b))
  | .sym d => symOf T d
  | _ => none

/-- An attributes Record: [[Writable]], [[Enumerable]], [[Configurable]]. -/
def attrRec (a : RAttrs) : Run M (Val M) :=
  newRec [(Known.fWritable, .bool a.writable), (Known.fEnumerable, .bool a.enumerable),
    (Known.fConfigurable, .bool a.configurable)]

/-- The intrinsic name with the enclosing % of object `i`. -/
def intrinsicName (T : RealmTable) (i : Nat) : Option (Val M) :=
  ((T.objs[i]?).bind (·.keys.head?)).map fun k => .str (M.strLit (T.fieldName k))

/-- A position in the objects' List, or ~empty~. -/
def posVal : Option Nat → Val M
  | some i => .math (M.ofNat i)
  | none => empty

/-- A property's Record; `inTable`: as IntrinsicObjects gives it ([[Object]], [[Get]], [[Set]]
positions), else as ClauseProperties gives it ([[Intrinsic]] the object's name). -/
def propRec (T : RealmTable) (inTable : Bool) (p : RProp) : Run M (Val M) := do
  let key ← optOr .sortError (keyVal T p.key)
  let some (kind, value, object, intr, created, gthis, get, set) := (match p.val with
    | .accessor g s => some (Known.eAccessor, empty, empty, empty, empty, false,
      (if inTable then posVal g else empty), (if inTable then posVal s else empty))
    | .data (.obj i) =>
      if inTable then some (Known.eData, empty, .math (M.ofNat i), empty, empty, false, empty, empty)
      else (intrinsicName T i).map fun n => (Known.eData, empty, empty, n, empty, false, empty, empty)
    | .data .globalThis => some (Known.eData, empty, empty, empty, empty, true, empty, empty)
    | .data (.created a) => some (Known.eData, empty, empty, empty, .clause a.clause, false, empty, empty)
    | .data v => (plainVal T v).map fun x => (Known.eData, x, empty, empty, empty, false, empty, empty)
    : Option (EnumId × Val M × Val M × Val M × Val M × Bool × Val M × Val M))
    | Run.stop .sortError
  newRec [(Known.fKey, key), (Known.fKind, .enum kind), (Known.fValue, value), (Known.fObject, object),
    (Known.fIntrinsic, intr), (Known.fCreated, created), (Known.fGlobalThis, .bool gthis),
    (Known.fGet, get), (Known.fSet, set), (Known.fWritable, .bool p.attrs.writable),
    (Known.fEnumerable, .bool p.attrs.enumerable), (Known.fConfigurable, .bool p.attrs.configurable),
    (Known.fOptional, .bool (p.annexB || p.optional)), (Known.fOmittable, .bool p.omittable),
    (Known.fClause, .clause p.clause)]

/-- Object `i`'s Record, as IntrinsicObjects gives it. -/
def objRec (T : RealmTable) (i : Nat) (o : RObj) : Run M (Val M) := do
  let props ← listOf (← o.props.mapM (propRec T true))
  let slotVals ← o.slots.mapM fun (f, v) => do
    newRec [(Known.fName, .field f), (Known.fValue, ← optOr .sortError (plainVal T v))]
  let base : List (FieldId × Val M) := [(Known.fIndex, .math (M.ofNat i)),
    (Known.fNames, ← listOf ((o.names ++ o.keys).map .field)),
    (Known.fPrototype, match o.proto with | some j => .math (M.ofNat j) | none => .null),
    (Known.fExotic, match o.kind with | .exotic c => .clause c | .ordinary => empty),
    (Known.fExtensible, .bool o.extensible), (Known.fSlots, ← listOf (o.slots.map (.field ·.1))),
    (Known.fSlotValues, ← listOf slotVals), (Known.fProperties, props)]
  match o.fn? with
  | none => newRec (base ++ [(Known.fBehaviour, empty)])
  | some f => do
    let name ← optOr .sortError (keyVal T f.name)
    newRec (base ++ [(Known.fBehaviour, match f.alg with | some a => .alg a | none => .clause o.clause),
      (Known.fLength, .math (M.ofNat f.length)), (Known.fName, name),
      (Known.fPrefix, match f.pfx with | some p => .str (M.strLit p) | none => empty),
      (Known.fConstructor, .bool f.ctor), (Known.fAsync, .bool f.async), (Known.fLengthAttributes, ← attrRec f.lengthAttrs),
      (Known.fNameAttributes, ← attrRec f.nameAttrs)])

/-- RealmIntrinsic(realm, name): realm.[[Intrinsics]]'s field named `name`, one of the objects' keys. -/
def realmIntrinsic (T : RealmTable) (realm : Val M) (s : M.Str) : Run M (Val M) := do
  match (T.objs.flatMap (·.keys)).find? fun k => M.strEq s (M.strLit (T.fieldName k)) with
  | some k => readField (← readField realm Known.fIntrinsics) k
  | none => Run.stop .sortError

/-- Whether `s` starts with the ASCII text `p`. -/
def strStarts (s : M.Str) (p : String) : Bool :=
  !M.lt (M.strLen s) (M.ofNat p.length) && M.strEq (M.strSub s (M.ofNat 0) (M.ofNat p.length)) (M.strLit p)

/-- Whether `s` is `p` followed by a path naming an object from object `i`: `%` ends it, `.k` goes
on through data property k whose value is an object; residue where it goes through an accessor or
a value created by steps (its object is the result of a call). The first argument is the code units of `s` not
yet matched for certain: each property name takes at least one. -/
def walkName (T : RealmTable) (s : M.Str) : List M.Math → Nat → String → Run M Bool
  | [], _, _ => return false
  | _ :: fuel, i, p => do
    if M.strEq s (M.strLit (p ++ "%")) then return true
    let some o := T.objs[i]? | return false
    for q in o.props do
      let .str k := q.key | continue
      let p' := p ++ "." ++ k
      unless M.strEq s (M.strLit (p' ++ "%")) || strStarts s (p' ++ ".") do continue
      match q.val with
      | .data (.obj j) => return ← walkName T s fuel j p'
      | .accessor _ _ | .data (.created _) => Run.stop .residue
      | _ => return false
    return false

/-- IsIntrinsicName(n): whether `n` is this specification's name of an intrinsic object (§6.1.7.4):
`%X%` for a name of Table 6 (the table's keys without a dot), or `%X.a.b%` along data properties. -/
def isIntrinsicName (T : RealmTable) (s : M.Str) : Run M (Val M) := do
  for (o, i) in T.objs.zipIdx do
    for k in o.keys do
      let n := T.fieldName k
      unless !n.contains '.' && n.endsWith "%" do continue
      let root := (n.dropEnd 1).toString
      if M.strEq s (M.strLit n) || strStarts s (root ++ ".") then
        return .bool (← walkName T s (seqList (M.strUnits s)) i root)
  return .bool false

/-- The realm primitives over the table `T`; none for any other. -/
def prim (T : RealmTable) (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pIntrinsicObjects then some (match vs with
    | [] => do listOf (← T.objs.zipIdx.mapM fun (o, i) => objRec T i o)
    | _ => Run.stop .sortError)
  else if p == Known.pClauseProperties then some (match vs with
    | [_, .clause c] => match T.clauseProps.lookup c with
      | some ps => do listOf (← ps.mapM (propRec T false))
      | none => Run.stop .residue
    | _ => Run.stop .sortError)
  else if p == Known.pRealmIntrinsic then some (match vs with
    | [realm, .str s] => realmIntrinsic T realm s
    | _ => Run.stop .sortError)
  else if p == Known.pSetFieldNamed then some (match vs with
    | [r, .field f, v] => do writeField r f v; return .enum Known.eUnused
    | _ => Run.stop .sortError)
  else if p == Known.pIsIntrinsicName then some (match vs with
    | [.str s] => isIntrinsicName T s
    | _ => Run.stop .sortError)
  else if p == Known.pWellKnownSymbol then some (match vs with
    | [.str s] => match T.symbols.find? (fun d => M.strEq s (M.strLit d)) >>= symOf T with
      | some v => pure v
      | none => Run.stop .sortError
    | _ => Run.stop .sortError)
  else none

end Ecma.Prims.Realm
