module

public import Engine.Model.Parse
public import Engine.Model.Parent
public import Engine.Model.Relabel
public import Engine.Model.OMapLaws
public import Engine.Model.Digits
public import Engine.Model.CharSet
public import Engine.Model.Bytes
public import Engine.Model.Radix
public import Ecma.Model.Laws

@[expose] public section

/-! # The engine's model -/

namespace Engine

open Ecma

open Engine Engine.Model in
/-- The engine's model: mathematical values as `MathVal`, Numbers as binary64 bit patterns, Strings as arrays of
code units, a store of cells in an array, and Parse Nodes with ParseText's parse. -/
@[reducible] def Impl : Model where
  Math := MathVal
  Num := Engine.Model.Num
  Big := Int
  Str := Array UInt16
  Sym := Nat × Option (Array UInt16)
  Addr := Nat
  Node := Engine.Model.Node
  Seq := Array
  Rec := WMap FieldId
  Props := WMap (Array UInt16 ⊕ (Nat × Option (Array UInt16)))
  Heap := Array
  Bytes := ByteArray

  ofNat n := .int n
  add := MathVal.add
  sub a b := MathVal.add a (MathVal.neg b)
  mul := MathVal.mul
  div := MathVal.div
  neg := MathVal.neg
  pow := MathVal.pow
  lt := MathVal.lt
  eq := MathVal.eq
  floor := MathVal.floor
  isInt := MathVal.isInt
  decExp x := .int (Digits.decExp x.toQ)
  sqrt := MathVal.sqrt
  pi := MathVal.piTimes 1
  fn := MathVal.mathFn

  numView a := Engine.Model.numView a.1
  numOf x := .of (MathVal.toNum x)
  numNaN := .nan
  numInf b := .of (Binary64.infinity b)
  numZero b := .of (Binary64.zero b)
  numAdd a b := .of (Binary64.add a.1 b.1)
  numSub a b := .of (Binary64.add a.1 (Num.of (Binary64.neg b.1)).1)
  numMul a b := .of (Binary64.mul a.1 b.1)
  numDiv a b := .of (Binary64.div a.1 b.1)
  numNeg a := .of (Binary64.neg a.1)
  numLt a b := Binary64.lt a.1 b.1
  numEq a b := Binary64.eq a.1 b.1
  numDigits x r := match r with
    | .int (.ofNat q) => let t := Digits.digits x.1 q; (.int t.1, t.2.1, .int t.2.2)
    | _ => (.int 0, 0, .int 0)

  bigOf := MathVal.bigOf
  bigVal b := .int b

  strLit := Engine.Model.utf16
  strLen s := .int s.size
  strAt s i := (MathVal.idx i).bind fun k => s[k]?.map fun u => .int u.toNat
  strConcat s t := s ++ t
  strSub s i j := match MathVal.idx i, MathVal.idx j with
    | some a, some b => s.extract a b
    | _, _ => #[]
  strOfUnit u := match MathVal.idx u with
    | some k => #[k.toUInt16]
    | none => #[]
  strRepeat := Engine.Model.strRepeat
  intToRadix := Engine.Model.intToRadix
  strEq s t := s == t
  strUnits s := s.map fun u => MathVal.int u.toNat

  symEq a b := a.1 == b.1 && a.2 == b.2
  symDesc s := s.2
  symNew k d := (k, d)
  addrEq a b := a == b

  nodeProd | .mk _ _ _ p _ _ _ _ => p
  nodeChild := Engine.Model.nodeChild
  nodeKids | .mk _ _ _ _ _ _ ks _ => ks.filterMap Prod.snd
  nodeDescendants := Engine.Model.descendants
  nodeNt | .mk _ _ _ _ n _ _ _ => n
  nodeSource | .mk _ _ _ _ _ _ _ t => t.toArray.map fun (c : Nat) => MathVal.int c
  nodeArgs | .mk _ _ _ _ _ ps _ _ => ps
  parse := Engine.parse
  cover := Engine.Model.Relabel.relabel
  nodeStamp | .mk k _ _ _ _ _ _ _ => k
  nodeSpan | .mk _ i j _ _ _ _ _ => (i, j)
  nodeParent := Engine.parent
  nodeAncestors := Engine.ancestors
  nodeHeight := Engine.treeHeight
  nodeEq := Node.same

  seqNil := #[]
  seqPush xs a := xs.push a
  seqCons a xs := #[a] ++ xs
  seqLen xs := .int xs.size
  seqGet xs i := (MathVal.idx i).bind fun k => xs[k]?
  seqSet xs i a := match MathVal.idx i with
    | some k => xs.setIfInBounds k a
    | none => xs
  seqConcat xs ys := xs ++ ys
  seqRemove xs i := match MathVal.idx i with
    | some k => xs.eraseIdxIfInBounds k
    | none => xs
  seqRepeat n a := match MathVal.idx n with
    | some k => Array.replicate k a
    | none => #[]
  seqFoldl f b xs := xs.foldl f b

  recEmpty := WMap.empty
  recGet := WMap.get
  recSet := WMap.put
  recDel := WMap.del
  recKeys := WMap.keys

  propsEmpty := WMap.empty
  propsGet := WMap.get
  propsPut := WMap.put
  propsDel := WMap.del
  propsKeys := WMap.keys

  heapEmpty := #[]
  heapAlloc h v := (h.size, h.push v)
  heapGet h a := h[a]?
  heapSet h a v := h.setIfInBounds a v

  scf? c := (MathVal.idx c).bind fun n => (Engine.scfPoint? n).map fun (d : Nat) => MathVal.int d
  toLower xs := (Engine.lowerPoints (xs.toList.filterMap MathVal.idx)).toArray.map fun (c : Nat) => MathVal.int c
  toUpper xs := (Engine.upperPoints (xs.toList.filterMap MathVal.idx)).toArray.map fun (c : Nat) => MathVal.int c
  propSet p v := do
    let nat : MathVal → Option Nat := fun | .int i => if 0 ≤ i then some i.toNat else none | _ => none
    let es ← Engine.PropSets.elements (← p.toList.mapM nat) (← v.toList.mapM nat)
    return (es.map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray
  propValue p v := do
    let nat : MathVal → Option Nat := fun | .int i => if 0 ≤ i then some i.toNat else none | _ => none
    let n ← Engine.Model.Unicode.propertyValueName? (← p.toList.mapM nat) (← v.toList.mapM nat)
    return (n.map fun (c : Nat) => MathVal.int c).toArray

  normalize f xs := ((Engine.normalizePoints f (xs.toList.filterMap MathVal.idx)).map fun (c : Nat) => MathVal.int c).toArray

  CharSet := Engine.Model.CharSet
  csEmpty := Engine.Model.csEmpty
  csAdd := Engine.Model.csAdd
  csInterval := Engine.Model.csInterval
  csUnion := Engine.Model.csUnion
  csInter := Engine.Model.csInter
  csDiff := Engine.Model.csDiff
  csHas := Engine.Model.csHas
  csSize := Engine.Model.csSize
  csGet := Engine.Model.csGet
  csAllSingle := Engine.Model.csAllSingle
  csSingles := Engine.Model.csSingles
  csFromProp := Engine.Model.csFromProp
  csNoScf := Engine.Model.csNoScf
  csCanonExtra := Engine.Model.csCanonExtra
  csHasCanon := Engine.Model.csHasCanon

  bytesZero := Engine.Model.bytesZero
  bytesLen := Engine.Model.bytesLen
  bytesGet := Engine.Model.bytesGet
  bytesSet := Engine.Model.bytesSet
  bytesFill := Engine.Model.bytesFill

end Engine
