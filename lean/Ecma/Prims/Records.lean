module

public import Ecma.State

@[expose] public section

/-!
# Notation primitives: Records, objects and slots

The primitives `Known.pComponent` … `Known.pPresent`: fields of Records,
internal slots and methods of objects, attributes of properties, new Records,
and presence of a value. `prim` dispatches by id.
-/

namespace Ecma.Prims.Records

variable {M : Model}

/-- The sorts whose values are not Records of the store. -/
def valueSorts : List SortId :=
  [Known.sComp, Known.sNumber, Known.sString, Known.sBoolean, Known.sSymbol, Known.sBigInt,
    Known.sObject, Known.sInteger, Known.sMath, Known.sXMath, Known.sNode, Known.sClosure,
    Known.sLangValue, Known.sPropKey, Known.sNormalComp, Known.sAbruptComp, Known.sThrowComp,
    Known.sReturnComp, Known.sUndefined, Known.sNull, Known.sNonNegInt]

/-- Whether an object's internal slot table has an entry for the name. -/
def slotPresent (f : FieldId) (o : Val M) : Run M (Val M) := do
  let (_, sl, _) ← objCell o
  return .bool (M.recGet sl f).isSome

/-- §6.2.2, §9.4: `the F component of e`, `e's [[F]]`: the field of a Record, the internal slot of an object, or the component of a Completion Record or an execution context. -/
def component : List (Val M) → Run M (Val M)
  | [e, .field f] => readField e f
  | _ => Run.stop .sortError

/-- §6.2.2: `e has a [[F]] field`: the Record has the field; a Completion Record has exactly [[Type]], [[Value]] and [[Target]]. -/
def hasField : List (Val M) → Run M (Val M)
  | [.field f, .ref a] => do
    match ← readCell a with
    | .record _ fs | .env _ fs _ => return .bool (M.recGet fs f).isSome
    | _ => Run.stop .sortError
  | [.field f, .comp _ _ _] =>
    Run.pure (.bool (f == Known.fType || f == Known.fValue || f == Known.fTarget))
  | _ => Run.stop .sortError

/-- §6.1.7.2: `O has a [[F]] internal slot`: the object has the internal slot. -/
def hasSlot : List (Val M) → Run M (Val M)
  | [.field f, o] => slotPresent f o
  | _ => Run.stop .sortError

/-- §6.1.7.2: `O has a [[M]] internal method`: the object has the internal method. -/
def hasMethod : List (Val M) → Run M (Val M)
  | [.field f, o] => slotPresent f o
  | _ => Run.stop .sortError

/-- §6.1.7.2: `O has [[A]], [[B]] and [[C]] internal slots`: the object has every internal slot of the List. -/
def hasSlots : List (Val M) → Run M (Val M)
  | [.ref l, o] => do
    let (_, sl, _) ← objCell o
    match ← readCell l with
    | .list xs _ =>
      match M.seqFoldl (fun acc v => match acc, v with
          | some b, .field f => some (b && (M.recGet sl f).isSome)
          | _, _ => none) (some true) xs with
      | some b => return .bool b
      | none => Run.stop .sortError
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.7.1: `the value of P's [[F]] attribute`: the attribute of an own property. -/
def attrValue : List (Val M) → Run M (Val M)
  | [p, .field f] => do
    let (_, _, fs) ← recOf p
    optOr .sortError (M.recGet fs f)
  | _ => Run.stop .sortError

/-- §10.2.3, §10.4.1.3, §10.4.6.12: `the internal slots listed in Table N`: the table's slot names,
which the program's tables give (`Ecma.Machine.tablePrim`); without them a residue. -/
def slotsListed : List (Val M) → Run M (Val M)
  | [_] => Run.stop .residue
  | _ => Run.stop .sortError

/-- §6.2.2: `a new R` of a Record sort: a new Record of that sort with no fields (a new List for the List sort);
at a type value of a sort or a sort and its modifiers, the program's (`newOfTy`). -/
def newRecord : List (Val M) → Run M (Val M)
  | [.sort s] =>
    if s == Known.sList then do return .ref (← alloc (.list M.seqNil 0))
    else if s == Known.sCharSet then do return .ref (← alloc (.charSet M.csEmpty))
    else if valueSorts.contains s then Run.stop .sortError
    else do return .ref (← alloc (.record s M.recEmpty))
  | [.ty (.sort ..) ..] => Run.stop .residue
  | .sort _ :: .sort _ :: _ => Run.stop .residue
  | _ => Run.stop .sortError

/-- §5.2: `x is present`: an optional parameter that was passed, a variable that is bound. -/
def present : List (Val M) → Run M (Val M)
  | [.absent] | [.missing] => Run.pure (.bool false)
  | [_] => Run.pure (.bool true)
  | _ => Run.stop .sortError

/-! The bindings of Environment Records (§9.1): a table from names to binding Records of the store. -/

/-- An Environment Record's cell: its address, kind, fields and bindings. -/
def bindsOf : Val M → Run M (M.Addr × SortId × M.Rec (Val M) × M.Props (Val M))
  | .ref a => do
    match ← readCell a with
    | .env k fs b => return (a, k, fs, b)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- A binding's name as the table's key. -/
def nameKey : Val M → Run M (M.Str ⊕ M.Sym)
  | .str s => return .inl s
  | _ => Run.stop .sortError

/-- NewBindingsRecord(kind): a new Environment Record of sort `kind` with no fields and no bindings. -/
def newBindingsRecord : List (Val M) → Run M (Val M)
  | [.sort k] => do return .ref (← alloc (.env k M.recEmpty M.propsEmpty))
  | _ => Run.stop .sortError

/-- BindingsHas(env, N): whether `env` has a binding for the name `N`. -/
def hasBinding : List (Val M) → Run M (Val M)
  | [e, n] => do
    let (_, _, _, b) ← bindsOf e
    return .bool (M.propsGet b (← nameKey n)).isSome
  | _ => Run.stop .sortError

/-- BindingFor(env, N): the binding Record for `N`; `env` has one. -/
def bindingFor : List (Val M) → Run M (Val M)
  | [e, n] => do
    let (_, _, _, b) ← bindsOf e
    optOr .assertFailed (M.propsGet b (← nameKey n))
  | _ => Run.stop .sortError

/-- AddBinding(env, N, b): `b` becomes `env`'s binding for `N`; `env` has none for `N`. -/
def addBinding : List (Val M) → Run M (Val M)
  | [e, n, x] => do
    let (a, k, fs, b) ← bindsOf e
    let key ← nameKey n
    if (M.propsGet b key).isSome then Run.stop .assertFailed
    else do
      writeCell a (.env k fs (M.propsPut b key x))
      return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- RemoveBinding(env, N): `env` no longer has a binding for `N`. -/
def removeBinding : List (Val M) → Run M (Val M)
  | [e, n] => do
    let (a, k, fs, b) ← bindsOf e
    writeCell a (.env k fs (M.propsDel b (← nameKey n)))
    return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- BindingNames(env): a new List of the names `env` has bindings for, in the order they were added. -/
def bindingNames : List (Val M) → Run M (Val M)
  | [e] => do
    let (_, _, _, b) ← bindsOf e
    listOf ((M.seqFoldl (fun acc k => match k with
      | .inl s => .str s :: acc
      | .inr y => .sym y :: acc) [] (M.propsKeys b)).reverse)
  | _ => Run.stop .sortError

/-- RecordFieldNames(r): a new List of the Record's field names, ascending by field id. -/
def recordFieldNames : List (Val M) → Run M (Val M)
  | [r] => do
    let (_, _, fs) ← recOf r
    listOf ((recFieldNames fs).map Val.field)
  | _ => Run.stop .sortError

/-- The primitives of Records, objects and slots, by id; `none` for any other id. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pComponent then some (component vs)
  else if p == Known.pHasField then some (hasField vs)
  else if p == Known.pHasSlot then some (hasSlot vs)
  else if p == Known.pHasMethod then some (hasMethod vs)
  else if p == Known.pHasSlots then some (hasSlots vs)
  else if p == Known.pAttrValue then some (attrValue vs)
  else if p == Known.pSlotsListed then some (slotsListed vs)
  else if p == Known.pNewRecord then some (newRecord vs)
  else if p == Known.pPresent then some (present vs)
  else if p == Known.pNewBindingsRecord then some (newBindingsRecord vs)
  else if p == Known.pBindingsHas then some (hasBinding vs)
  else if p == Known.pBindingFor then some (bindingFor vs)
  else if p == Known.pAddBinding then some (addBinding vs)
  else if p == Known.pRemoveBinding then some (removeBinding vs)
  else if p == Known.pBindingNames then some (bindingNames vs)
  else if p == Known.pRecordFieldNames then some (recordFieldNames vs)
  else none

end Ecma.Prims.Records
