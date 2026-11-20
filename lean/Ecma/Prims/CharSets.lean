module

public import Ecma.State
public import Ecma.Prims.Strings

@[expose] public section

/-!
# Notation primitives: CharSets

The prose notation of §22.2.2.1 over characters and CharSets. A character is
its character value, a mathematical value (an integer 0–0x10FFFF). A
CharSetElement is a character, or (when [[UnicodeSets]] is *true*) a List of
characters, a List of one character being the same element as that character.
A CharSet is a canonical `Cell.charSet` value (`M.CharSet`) in the store.
-/

namespace Ecma.Prims.CharSets

section
variable {M : Model}

/-- A character value (§22.2.2): an integer in `[0, 0x10FFFF]`. -/
def isChar (m : M.Math) : Bool :=
  M.isInt m && !M.lt m (M.ofNat 0) && !M.lt (M.ofNat 0x10FFFF) m

/-- A CharSetElement as its sequence of characters, or `none` when `v` is not a CharSetElement. -/
def elemSeq? (v : Val M) : Run M (Option (M.Seq M.Math)) :=
  match v with
  | .math c => Run.pure (if isChar c then some (M.seqPush M.seqNil c) else none)
  | .ref a => do
    match ← readCell a with
    | .list xs _ =>
      return M.seqFoldl (fun acc x => match acc, x with
        | some s, .math c => if isChar c then some (M.seqPush s c) else none
        | _, _ => none) (some M.seqNil) xs
    | _ => return none
  | _ => Run.pure none

/-- A CharSetElement as its sequence of characters; stops with a sort error otherwise. -/
def elemSeq (v : Val M) : Run M (M.Seq M.Math) := do
  optOr .sortError (← elemSeq? v)

/-- A CharSetElement sequence as a Value: a character for length 1, else a new List of characters. -/
def seqVal (sq : M.Seq M.Math) : Run M (Val M) :=
  if M.eq (M.seqLen sq) (M.ofNat 1) then
    match M.seqGet sq (M.ofNat 0) with
    | some c => Run.pure (.math c)
    | none => Run.stop .sortError
  else do
    return .ref (← alloc (.list (M.seqFoldl (fun r c => M.seqPush r (.math c)) M.seqNil sq) 0))

/-- The address and CharSet of a `Cell.charSet` reference. -/
def charSetCell (v : Val M) : Run M (M.Addr × M.CharSet) :=
  match v with
  | .ref a => do
    match ← readCell a with
    | .charSet cs => Run.pure (a, cs)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- Allocate a CharSet cell. -/
def newCharSet (cs : M.CharSet) : Run M (Val M) := do
  return .ref (← alloc (.charSet cs))

/-- §22.2.2.1 "the union (0) or intersection (1) of CharSets a and b". -/
def charSetUnion (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.choice 0, a, b] => do
    let (_, ca) ← charSetCell a
    let (_, cb) ← charSetCell b
    newCharSet (M.csUnion ca cb)
  | [.choice 1, a, b] => do
    let (_, ca) ← charSetCell a
    let (_, cb) ← charSetCell b
    newCharSet (M.csInter ca cb)
  | _ => Run.stop .sortError

/-- §22.2.2.1 "a one-element CharSet containing c": a new CharSet whose sole element is c. -/
def charSetOne (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.choice _, c] | [c] => do
    let sq ← elemSeq c
    newCharSet (M.csAdd M.csEmpty sq)
  | _ => Run.stop .sortError

/-- The union of the CharSets in a List. -/
def unionOf (l : Val M) : Run M (Val M) :=
  match l with
  | .ref a => do
    match ← readCell a with
    | .list xs _ => do
      let cs ← Run.seqFold (fun acc v => do
        let (_, c) ← charSetCell v
        return M.csUnion acc c) M.csEmpty xs
      newCharSet cs
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §22.2.2.1 "the union of CharSets l": the union of the CharSets in the List l. -/
def charSetUnionAll (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.choice _, l] | [l] => unionOf l
  | _ => Run.stop .sortError

/-- §22.2.2 "the character whose character value is e", and "the character e". -/
def char (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.math c] => if isChar c then Run.pure (.math c) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §22.2.2 "the character value of character c": the numeric value of its code point; a
sequence of one character is that character. -/
def charValue (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [c] => do
    let s ← elemSeq c
    if M.eq (M.seqLen s) (M.ofNat 1) then
      match M.seqGet s (M.ofNat 0) with
      | some x => Run.pure (.math x)
      | none => Run.stop .sortError
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- A Unicode property or value name: a List of code points, or a String's code points (§6.1.4). -/
def nameSeq (v : Val M) : Run M (M.Seq M.Math) :=
  match v with
  | .str t => Run.pure (Strings.strPoints t)
  | .ref a => do
    match ← readCell a with
    | .list xs _ => optOr .sortError (M.seqFoldl (fun acc x => match acc, x with
        | some s, .math c => if isChar c then some (M.seqPush s c) else none
        | _, _ => none) (some M.seqNil) xs)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- A sequence of a list's elements, in order. -/
def seqOfList {α : Type} (l : List α) : M.Seq α := l.foldl M.seqPush M.seqNil

/-- §22.2.2.9 "the CharSet containing all CharSetElements whose character database definition
includes the property p with value v": a new CharSet with a character per one-character element
and a new List per longer one; a name pair that is no property value stops. -/
def propertyCharSet (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [p, v] => do
    let cs ← optOr .sortError (M.csFromProp (← nameSeq p) (← nameSeq v))
    newCharSet cs
  | _ => Run.stop .sortError

/-- IsPropertyValueAlias(p, v): whether PropertyValueAliases.txt lists the value name v for the
property named p. -/
def isPropertyValueAlias (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [p, v] => do return .bool (M.propValue (← nameSeq p) (← nameSeq v)).isSome
  | _ => Run.stop .sortError

/-- CanonicalPropertyValue(p, v): a new List of the code points of the long name of the value v
names for the property p names; a pair that names none stops. -/
def canonicalPropertyValue (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [p, v] => do
    let n ← optOr .sortError (M.propValue (← nameSeq p) (← nameSeq v))
    return .ref (← alloc (.list (M.seqFoldl (fun r c => M.seqPush r (.math c)) M.seqNil n) 0))
  | _ => Run.stop .sortError

/-- SimpleCaseFold(c): the simple or common case folding of the character c in CaseFolding.txt
(§22.2.2.7.3 step 1.a), or ~empty~ when there is none. -/
def simpleCaseFold (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.math c] =>
    if isChar c then Run.pure (match M.scf? c with
      | some d => .math d
      | none => .enum Known.eEmpty)
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- scf(c) (§22.2.2.7.3): the simple case folding of the code point c, c where there is none. -/
def scf (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.math c] => if isChar c then Run.pure (.math ((M.scf? c).getD c)) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- EmptyCharSet(): a new empty CharSet. -/
def emptyCharSet : List (Val M) → Run M (Val M)
  | [] => newCharSet M.csEmpty
  | _ => Run.stop .sortError

/-- CharSetInterval(i, j): all characters with character value in `[i, j]`. -/
def charSetInterval : List (Val M) → Run M (Val M)
  | [.math i, .math j] => if isChar i && isChar j then newCharSet (M.csInterval i j) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- CharSetMinus(a, b): elements of `a` not in `b`. -/
def charSetMinus : List (Val M) → Run M (Val M)
  | [a, b] => do
    let (_, ca) ← charSetCell a
    let (_, cb) ← charSetCell b
    newCharSet (M.csDiff ca cb)
  | _ => Run.stop .sortError

/-- CharSetAllSingle(cs): whether every CharSetElement of `cs` is a single character. -/
def charSetAllSingle : List (Val M) → Run M (Val M)
  | [a] => do
    let (_, cs) ← charSetCell a
    return .bool (M.csAllSingle cs)
  | _ => Run.stop .sortError

/-- CharSetSingles(cs): single-character elements of `cs`. -/
def charSetSingles : List (Val M) → Run M (Val M)
  | [a] => do
    let (_, cs) ← charSetCell a
    newCharSet (M.csSingles cs)
  | _ => Run.stop .sortError

/-- CharSetNoScf(): all Unicode code points `c` with `scf(c) = c`. -/
def charSetNoScf : List (Val M) → Run M (Val M)
  | [] => newCharSet M.csNoScf
  | _ => Run.stop .sortError

/-- CharSetCanonExtra(cs, u): characters `c` not in `cs` whose case-folded Canonicalize(`c`, `u`) is in `cs`. -/
def charSetCanonExtra : List (Val M) → Run M (Val M)
  | [a, .bool u] => do
    let (_, cs) ← charSetCell a
    newCharSet (M.csCanonExtra cs u)
  | _ => Run.stop .sortError

/-- CharSetHasCanonical(cs, cc, u, ic): whether `cs` has a single character `a` with Canonicalize(`a`, `u`, `ic`) = `cc`. -/
def charSetHasCanonical : List (Val M) → Run M (Val M)
  | [a, .math cc, .bool u, .bool ic] =>
    if isChar cc then do
      let (_, cs) ← charSetCell a
      return .bool (M.csHasCanon cs cc u ic)
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- IsCharSet(v): whether `v` is a `CharSet`. -/
def isCharSet : List (Val M) → Run M (Val M)
  | [.ref a] => do
    match ← readCell a with
    | .charSet _ => return .bool true
    | _ => return .bool false
  | [_] => return .bool false
  | _ => Run.stop .sortError

/-- The CharSets family's primitives, by id; `none` for another family's. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pCharSetUnion then some (charSetUnion vs)
  else if p == Known.pCharSetOne then some (charSetOne vs)
  else if p == Known.pCharSetUnionAll then some (charSetUnionAll vs)
  else if p == Known.pChar then some (char vs)
  else if p == Known.pCharValue then some (charValue vs)
  else if p == Known.pSimpleCaseFold then some (simpleCaseFold vs)
  else if p == Known.pScf then some (scf vs)
  else if p == Known.pPropertyCharSet then some (propertyCharSet vs)
  else if p == Known.pIsPropertyValueAlias then some (isPropertyValueAlias vs)
  else if p == Known.pCanonicalPropertyValue then some (canonicalPropertyValue vs)
  else if p == Known.pEmptyCharSet then some (emptyCharSet vs)
  else if p == Known.pCharSetInterval then some (charSetInterval vs)
  else if p == Known.pCharSetMinus then some (charSetMinus vs)
  else if p == Known.pCharSetAllSingle then some (charSetAllSingle vs)
  else if p == Known.pCharSetSingles then some (charSetSingles vs)
  else if p == Known.pCharSetNoScf then some (charSetNoScf vs)
  else if p == Known.pCharSetCanonExtra then some (charSetCanonExtra vs)
  else if p == Known.pCharSetHasCanonical then some (charSetHasCanonical vs)
  else if p == Known.pIsCharSet then some (isCharSet vs)
  else none

end

end Ecma.Prims.CharSets
