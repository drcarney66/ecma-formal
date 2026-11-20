module

public import Ecma.Ops.Parse

@[expose] public section

/-!
# The notation's primitives, by id

`prim p vs`: the primitive `p` of the values `vs`, each family's in its own module (`Ecma.Prims`).
-/

namespace Ecma

variable {M : Model}

/-- The primitives of §5.2.6 and the List mutations, on the arguments as uses see them. -/
def primOn (p : PrimId) (vs : List (Val M)) : Run M (Val M) :=
  if p == Known.pF then match vs with
    | [.math x] => Run.pure (.num (if M.eq x (M.ofNat 0) then M.numZero false else M.numOf x))
    | [.posInf] => Run.pure (.num (M.numInf false))
    | [.negInf] => Run.pure (.num (M.numInf true))
    | _ => Run.stop .sortError
  else if p == Known.pR then match vs with
    | [.num n] => match M.numView n with
      | .finite x => Run.pure (.math x)
      | .posZero => Run.pure (.math (M.ofNat 0))
      | .negZero => Run.pure (.math (M.ofNat 0))
      | _ => Run.stop .sortError
    | [.big b] => Run.pure (.math (M.bigVal b))
    | _ => Run.stop .sortError
  else if p == Known.pZ then match vs with
    | [.math x] => bigFor x
    | _ => Run.stop .sortError
  else if p == Known.pAbs then match vs with
    | [.math x] => Run.pure (.math (if M.lt x (M.ofNat 0) then M.neg x else x))
    | _ => Run.stop .sortError
  else if p == Known.pFloor then match vs with
    | [.math x] => Run.pure (.math (M.floor x))
    | _ => Run.stop .sortError
  else if p == Known.pMin then match vs with
    | x :: ys@(_ :: _) => ys.foldlM (fun a y => do return if ← relOp .lt y a then y else a) x
    | _ => Run.stop .sortError
  else if p == Known.pMax then match vs with
    | x :: ys@(_ :: _) => ys.foldlM (fun a y => do return if ← relOp .lt a y then y else a) x
    | _ => Run.stop .sortError
  else if p == Known.pTruncate then match vs with
    | [.math x] => Run.pure (.math (if M.lt x (M.ofNat 0) then M.neg (M.floor (M.neg x)) else M.floor x))
    | _ => Run.stop .sortError
  else if p == Known.pAppend then match vs with
    | [x, .ref a] => do
      match ← readCell a with
      | .list xs _ => do writeList a (M.seqPush xs x); return .enum Known.eUnused
      | _ => Run.stop .sortError
    | _ => Run.stop .sortError
  else if p == Known.pPrepend then match vs with
    | [x, .ref a] => do
      match ← readCell a with
      | .list xs _ => do writeList a (M.seqCons x xs); return .enum Known.eUnused
      | _ => Run.stop .sortError
    | _ => Run.stop .sortError
  else if p == Known.pLength then match vs with
    | [.ref a] => do
      match ← readCell a with
      | .list xs _ => return .math (M.seqLen xs)
      | .block bs => return .math (M.bytesLen bs)
      | .charSet cs => return .math (M.csSize cs)
      | _ => Run.stop .sortError
    | [.str s] => Run.pure (.math (M.strLen s))
    | _ => Run.stop .sortError
  else if p == Known.pClamp then match vs with
    | [x, lo, hi] => do
      if ← relOp .lt x lo then return lo
      else if ← relOp .lt hi x then return hi
      else return x
    | _ => Run.stop .sortError
  else if p == Known.pOwnLookup then match vs with
    | [o, k] => ownLookup o k
    | _ => Run.stop .sortError
  else if p == Known.pOwnCreate then match vs with
    | [o, k, d, .enum kind] => ownPut true o k d kind []
    | _ => Run.stop .sortError
  else if p == Known.pOwnReplace then match vs with
    | [o, k, d, .enum kind, c, e] => ownPut false o k d kind [(Known.fConfigurable, c), (Known.fEnumerable, e)]
    | _ => Run.stop .sortError
  else if p == Known.pOwnSetAttribute then match vs with
    | [o, k, d] => ownSetAttrs o k d
    | _ => Run.stop .sortError
  else if p == Known.pOwnRemove then match vs with
    | [o, k] => ownRemove o k
    | _ => Run.stop .sortError
  else if p == Known.pPropertyIsKind then match vs with
    | [v, .enum e] => do
      let (_, _, fs) ← recOf v
      return .bool (M.recGet fs (if e == Known.eAccessor then Known.fGetter else Known.fValue)).isSome
    | _ => Run.stop .sortError
  else if p == Known.pOwnHas then match vs with
    | [o, k] => ownHas o k
    | _ => Run.stop .sortError
  else if p == Known.pOneIndexedList then match vs with
    | [.math k, v] =>
      if M.isInt k && !M.lt k (M.ofNat 0) then do return .ref (← alloc (.list (M.seqRepeat k v) 1))
      else Run.stop .sortError
    | _ => Run.stop .sortError
  else if p == Known.pMakeObject then match vs with
    | [.ref l] => do
      match ← readCell l with
      | .list xs _ =>
        match M.seqFoldl (fun acc v => match acc, v with
            | some r, .field f => some (M.recSet r f .undefined)
            | _, _ => none) (some M.recEmpty) xs with
        | some sl => do return .obj (← alloc (.object sl M.propsEmpty))
        | none => Run.stop .sortError
      | _ => Run.stop .sortError
    | _ => Run.stop .sortError
  else if p == Known.pBuiltinFunctionSlots then match vs with
    | [] => listOf ([Known.fPrototype, Known.fExtensible, Known.fRealm, Known.fInitialName, Known.fAsync].map .field)
    | _ => Run.stop .sortError
  else if p == Known.pNewSymbol then match vs with
    | [d] => do
      let desc ← match d with
        | .str t => Run.pure (some t)
        | .undefined => Run.pure none
        | _ => Run.stop .sortError
      let s ← Run.get
      Run.set { s with syms := s.syms + 1 }
      return .sym (M.symNew s.syms desc)
    | _ => Run.stop .sortError
  else if p == Known.pKeysOrdered then match vs with
    | [o, .math ord] => keysOrdered o ord
    | _ => Run.stop .sortError
  else if p == Known.pHasNoFields then match vs with
    | [d] => do
      let (_, _, fs) ← recOf d
      return .bool (recIsEmpty fs)
    | _ => Run.stop .sortError
  else if p == Known.pIsOrdinaryMethod then match vs with
    | [.alg a, .clause c] => Run.pure (.bool (a.clause == c))
    | [_, .clause _] => Run.pure (.bool false)
    | _ => Run.stop .sortError
  else if p == Known.pEmptyString then Run.pure (.str (M.strLit ""))
  else if p == Known.pConcat then Prims.Strings.strOfUnits vs
  else if p == Known.pIsJSONText then isJSONText vs
  else match Prims.Lists.prim p vs <|> Prims.Strings.prim p vs <|> Prims.CharSets.prim p vs <|>
      Prims.Records.prim p vs <|> Prims.Context.prim p vs <|> Prims.Nodes.prim p vs <|>
      Prims.Numbers.prim p vs with
    | some r => r
    | none => Run.stop .residue

/-- A primitive: `is present` sees a parameter not passed, every other one *undefined* (§18). -/
def prim (p : PrimId) (vs : List (Val M)) : Run M (Val M) :=
  primOn p (if p == Known.pPresent then vs else vs.map Val.used)

/-- A field of a Record literal; absent fields are ~empty~. -/
def look (f : FieldId) : List (FieldId × Val M) → Val M
  | [] => .enum Known.eEmpty
  | (g, v) :: r => if g == f then v else look f r

end Ecma
