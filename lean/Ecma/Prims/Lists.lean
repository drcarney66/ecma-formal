module

public import Ecma.State
public import Ecma.Prims.CharSets

@[expose] public section

/-!
# The List notation's primitives

The notation of §6.2.2 (Lists) defined, with "a copy of" (§5.2), "is empty" and
"contains" on Strings (§6.1.4), and the byte store of §6.2.9. A List, a Set and a Data Block
are List cells of the store; a Data Block's elements are its bytes, as mathematical values.
Each primitive takes its semantic arguments in the table's order; a words choice is `Val.choice`.
-/

namespace Ecma.Prims.Lists

variable {M : Model}

/-- The address and elements of a List value. -/
def listCell (v : Val M) : Run M (M.Addr × M.Seq (Val M)) :=
  match v with
  | .ref a => do
    match ← readCell a with
    | .list xs _ => Run.pure (a, xs)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The elements, first to last, folded by a step that runs. -/
def foldRun {α β : Type} (f : β → α → Run M β) (b : β) (xs : M.Seq α) : Run M β :=
  Run.seqFold f b xs

/-- The same element: Lists (a CharSetElement's characters) by their elements, any other value
by `Val.same`. -/
def sameElem (x y : Val M) : Run M Bool :=
  match x, y with
  | .ref a, .ref b => do
    if M.addrEq a b then return true
    match ← readCell a, ← readCell b with
    | .list xs _, .list ys _ =>
      let l := M.seqFoldl (fun l v => l ++ [v]) [] xs
      let r := M.seqFoldl (fun l v => l ++ [v]) [] ys
      return l.length == r.length && (l.zip r).all fun (u, v) => Val.same u v
    | _, _ => return false
  | _, _ => return Val.same x y

/-- Whether some element is the same element as `x`. -/
def hasElem (x : Val M) (xs : M.Seq (Val M)) : Run M Bool :=
  foldRun (fun b v => if b then Run.pure true else sameElem v x) false xs

/-- 0 and 1. -/
def zero : M.Math := M.ofNat 0
def one : M.Math := M.ofNat 1

/-- §6.2.2 "a new empty List": a List with no elements. -/
def listNew : List (Val M) → Run M (Val M)
  | [] => listOf []
  | _ => Run.stop .sortError

/-- §6.2.2 "the list-concatenation of A, B, …": a new List of the arguments' elements, in order. -/
def listConcat : List (Val M) → Run M (Val M)
  | [l] => do
    let (_, ls) ← listCell l
    let ys ← foldRun (fun acc v => do
      let (_, xs) ← listCell v
      return M.seqConcat acc xs) M.seqNil ls
    return .ref (← alloc (.list ys 0))
  | _ => Run.stop .sortError

/-- §6.2.2 "the number of elements in L". -/
def listLen : List (Val M) → Run M (Val M)
  | [.ref a] => do
    match ← readCell a with
    | .list xs _ => return .math (M.seqLen xs)
    | .block bs => return .math (M.bytesLen bs)
    | .charSet cs => return .math (M.csSize cs)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.4: whether the String `t` occurs in `s` at some index. -/
def strHas (s t : M.Str) : Bool :=
  let n := M.strLen t
  (M.seqFoldl (fun (acc : Bool × M.Math) _ =>
    (acc.1 || (!M.lt (M.strLen s) (M.add acc.2 n) && M.strEq (M.strSub s acc.2 (M.add acc.2 n)) t),
      M.add acc.2 (M.ofNat 1))) (M.strEq t (M.strLit ""), M.ofNat 0) (M.strUnits s)).1

/-- §6.2.2, §6.1.4 "S contains x": some element of a List is x; a CharSet contains a CharSetElement;
a String contains a code unit or a String; a non-empty sequence of code points (source text, §11)
contains a code literal (`` `u` ``, §5.1.6) of one code point when one of its elements is that code point. -/
def contains : List (Val M) → Run M (Val M)
  | [x, .ref a] => do
    match ← readCell a with
    | .list xs _ =>
      let points := M.lt (M.ofNat 0) (M.seqLen xs) &&
        M.seqFoldl (fun b v => b && match v with | .math _ => true | _ => false) true xs
      match x, points with
      | .str t, true =>
        let us := M.strUnits t
        if M.eq (M.seqLen us) one then
          match M.seqGet us zero with
          | some u => return .bool (← hasElem (.math u) xs)
          | none => Run.stop .sortError
        else Run.stop .residue
      | _, _ => return .bool (← hasElem x xs)
    | .charSet cs => match ← CharSets.elemSeq? x with
      | some sq => return .bool (M.csHas cs sq)
      | none => return .bool false
    | _ => Run.stop .sortError
  | [.math u, .str s] => Run.pure (.bool (M.seqFoldl (fun b v => b || M.eq v u) false (M.strUnits s)))
  | [.str t, .str s] => Run.pure (.bool (strHas s t))
  | [_, .node _] => Run.stop .residue
  | _ => Run.stop .sortError

/-- §6.1.4: the number of code points of a String, a surrogate pair counting once. -/
def codePoints (s : M.Str) : M.Math :=
  let high (u : M.Math) := !M.lt u (M.ofNat 0xD800) && M.lt u (M.ofNat 0xDC00)
  let low (u : M.Math) := !M.lt u (M.ofNat 0xDC00) && M.lt u (M.ofNat 0xE000)
  (M.seqFoldl (fun (acc : M.Math × Bool) u =>
    if acc.2 && low u then (acc.1, false) else (M.add acc.1 (M.ofNat 1), high u))
    (M.ofNat 0, false) (M.strUnits s)).1

/-- §6.2.2 "the sole / first / last element of L"; "sole" asserts one element, the others a
non-empty List. -/
def listElem : List (Val M) → Run M (Val M)
  | [.choice w, .ref a] => do
    match ← readCell a with
    | .list xs _ =>
      let n := M.seqLen xs
      if w == 0 then
        if M.eq n one then optOr .assertFailed (M.seqGet xs zero) else Run.stop .assertFailed
      else if w == 1 then optOr .assertFailed (M.seqGet xs zero)
      else if w == 2 then
        if M.lt zero n then optOr .assertFailed (M.seqGet xs (M.sub n one)) else Run.stop .assertFailed
      else Run.stop .sortError
    | .charSet cs =>
      if w == 0 && M.eq (M.csSize cs) one then
        CharSets.seqVal (← optOr .assertFailed (M.csGet cs zero))
      else if w == 0 then Run.stop .assertFailed
      else Run.stop .sortError
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.2.2 "a List whose sole element is e". -/
def listOf1 : List (Val M) → Run M (Val M)
  | [e] => listOf [e]
  | _ => Run.stop .sortError

/-- §5.2 "a copy of e": a new List with the same elements, a new CharSet, or a new Record of the same
kind with the same fields. -/
def copy : List (Val M) → Run M (Val M)
  | [.ref a] => do
    match ← readCell a with
    | .list xs o => return .ref (← alloc (.list xs o))
    | .block bs => return .ref (← alloc (.block bs))
    | .charSet cs => return .ref (← alloc (.charSet cs))
    | .record k fs => return .ref (← alloc (.record k fs))
    | .env k fs b => return .ref (← alloc (.env k fs b))
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.2.2, §6.1.4 "e is empty": a List or CharSet with no elements, or a String of length 0. -/
def isEmpty : List (Val M) → Run M (Val M)
  | [.ref a] => do
    match ← readCell a with
    | .list xs _ => return .bool (M.eq (M.seqLen xs) zero)
    | .block bs => return .bool (M.eq (M.bytesLen bs) zero)
    | .charSet cs => return .bool (M.eq (M.csSize cs) zero)
    | _ => Run.stop .sortError
  | [.str s] => Run.pure (.bool (M.eq (M.strLen s) zero))
  | _ => Run.stop .sortError

/-- §6.2.2 "A, B, … have the same number of elements": over a List of Lists. -/
def sameLength : List (Val M) → Run M (Val M)
  | [l] => do
    let (_, ls) ← listCell l
    let r ← foldRun (fun (acc : Option M.Math × Bool) v => do
      let (_, xs) ← listCell v
      let n := M.seqLen xs
      return match acc.1 with
        | none => (some n, acc.2)
        | some m => (some m, acc.2 && M.eq m n)) (none, true) ls
    return .bool r.2
  | _ => Run.stop .sortError

/-- §6.2.2 "the element of L whose [[F]] is v": the one element whose field F is v. -/
def listFind : List (Val M) → Run M (Val M)
  | [.field f, l, v] => do
    let (_, xs) ← listCell l
    let found ← foldRun (fun (acc : List (Val M)) x => do
      let y ← readField x f
      return if Val.same y v then x :: acc else acc) [] xs
    match found with
    | [x] => Run.pure x
    | _ => Run.stop .assertFailed
  | _ => Run.stop .sortError

/-- §6.2.9 NewDataBlock(n): a new Data Block of n bytes, each 0, for a non-negative integer n. -/
def newDataBlock : List (Val M) → Run M (Val M)
  | [.math n] =>
    if M.isInt n && !M.lt n zero then do return .ref (← alloc (.block (M.bytesZero n)))
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.2.9 SetAllBytes(block, v): every byte of the Data Block `block` set to the byte `v`. -/
def setAllBytes : List (Val M) → Run M (Val M)
  | [.ref a, .math v] =>
    if M.isInt v && !M.lt v zero && M.lt v (M.ofNat 256) then do
      modifyBlock a (M.bytesFill · v)
      return .enum Known.eUnused
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.2.2, §6.1.4, §6.2.9 "the number of (elements | code units | code points | bytes) in e":
a List's or a Data Block's length, a String's length, or its or a Parse Node's code points. -/
def count : List (Val M) → Run M (Val M)
  | [.choice w, e] =>
    if w == 0 || w == 3 then listLen [e]
    else if w == 1 then match e with
      | .str s => Run.pure (.math (M.strLen s))
      | _ => Run.stop .sortError
    else if w == 2 then match e with
      | .ref _ => listLen [e]
      | .str t => Run.pure (.math (codePoints t))
      | .node nd => Run.pure (.math (M.seqLen (M.nodeSource nd)))
      | _ => Run.stop .sortError
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.2.2 "Insert e as the first element of L". -/
def insert : List (Val M) → Run M (Val M)
  | [e, l] => do
    let (a, xs) ← listCell l
    writeList a (M.seqCons e xs)
    return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- The index of the first element that is the same value as `x`. -/
def indexOf (x : Val M) (xs : M.Seq (Val M)) : Option M.Math :=
  (M.seqFoldl (fun (acc : Option M.Math × M.Math) v =>
    match acc.1 with
    | some _ => acc
    | none => (if Val.same v x then some acc.2 else none, M.add acc.2 one)) (none, zero) xs).1

/-- §6.2.2 "Remove e from L": the element that is e, which L contains. -/
def removeElem : List (Val M) → Run M (Val M)
  | [e, l] => do
    let (a, xs) ← listCell l
    let i ← optOr .assertFailed (indexOf e xs)
    writeList a (M.seqRemove xs i)
    return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- §6.2.2 "Remove the first element from L"; L is not empty. -/
def removeFirst : List (Val M) → Run M (Val M)
  | [l] => do
    let (a, xs) ← listCell l
    if M.lt zero (M.seqLen xs) then
      writeList a (M.seqRemove xs zero)
      return .enum Known.eUnused
    else Run.stop .assertFailed
  | _ => Run.stop .sortError

/-- §6.2.2 "Remove the last element of L"; L is not empty. -/
def removeLast : List (Val M) → Run M (Val M)
  | [l] => do
    let (a, xs) ← listCell l
    let n := M.seqLen xs
    if M.lt zero n then
      writeList a (M.seqRemove xs (M.sub n one))
      return .enum Known.eUnused
    else Run.stop .assertFailed
  | _ => Run.stop .sortError

/-- §6.2.2 "Reverse the order of the elements of L", in place. -/
def reverse : List (Val M) → Run M (Val M)
  | [l] => do
    let (a, xs) ← listCell l
    writeList a (M.seqFoldl (fun r v => M.seqCons v r) M.seqNil xs)
    return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- §6.2.2 "Replace the element of L whose value is old with an element whose value is new", in
place: the first element that is old, which L contains. -/
def replaceElem : List (Val M) → Run M (Val M)
  | [l, old, new] => do
    let (a, xs) ← listCell l
    let i ← optOr .assertFailed (indexOf old xs)
    writeList a (M.seqSet xs i new)
    return .enum Known.eUnused
  | _ => Run.stop .sortError

/-- §6.2.2 "Add e to S": S, a List or CharSet without duplicates, gets e last unless it contains it. -/
def setAdd : List (Val M) → Run M (Val M)
  | [e, .ref a] => do
    match ← readCell a with
    | .list xs _ =>
      if ← hasElem e xs then return .enum Known.eUnused
      writeList a (M.seqPush xs e)
      return .enum Known.eUnused
    | .charSet cs =>
      let sq ← CharSets.elemSeq e
      writeCell a (.charSet (M.csAdd cs sq))
      return .enum Known.eUnused
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.2.9 "Store the individual bytes of bytes into block, starting at block[start]": the bytes,
in order, at start and the indices after it, which are within the block. -/
def storeBytes : List (Val M) → Run M (Val M)
  | [e, .ref a, .math start] => do
    let (_, bs) ← listCell e
    let bytes ← optOr .sortError (M.seqFoldl (fun acc v => match acc, v with
      | some ls, .math b =>
        if M.isInt b && !M.lt b zero && M.lt b (M.ofNat 256) then some (ls ++ [b]) else none
      | _, _ => none) (some []) bs)
    match ← readCell a with
    | .block ds =>
      if !M.isInt start || M.lt start zero || M.lt (M.bytesLen ds) (M.add start (M.seqLen bs)) then
        Run.stop .assertFailed
      else
        modifyBlock a fun ds =>
          (bytes.foldl (fun (acc : M.Bytes × M.Math) b => (M.bytesSet acc.1 acc.2 b, M.add acc.2 one))
            (ds, start)).1
        return .enum Known.eUnused
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The Lists family: `some` of the primitive's meaning for ids 28–46, `none` for the others. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pListNew then some (listNew vs)
  else if p == Known.pListConcat then some (listConcat vs)
  else if p == Known.pListLen then some (listLen vs)
  else if p == Known.pContains then some (contains vs)
  else if p == Known.pListElem then some (listElem vs)
  else if p == Known.pListOf1 then some (listOf1 vs)
  else if p == Known.pCopy then some (copy vs)
  else if p == Known.pIsEmpty then some (isEmpty vs)
  else if p == Known.pSameLength then some (sameLength vs)
  else if p == Known.pListFind then some (listFind vs)
  else if p == Known.pCount then some (count vs)
  else if p == Known.pInsert then some (insert vs)
  else if p == Known.pRemoveElem then some (removeElem vs)
  else if p == Known.pRemoveFirst then some (removeFirst vs)
  else if p == Known.pRemoveLast then some (removeLast vs)
  else if p == Known.pReverse then some (reverse vs)
  else if p == Known.pReplaceElem then some (replaceElem vs)
  else if p == Known.pSetAdd then some (setAdd vs)
  else if p == Known.pStoreBytes then some (storeBytes vs)
  else if p == Known.pNewDataBlock then some (newDataBlock vs)
  else if p == Known.pSetAllBytes then some (setAllBytes vs)
  else none

end Ecma.Prims.Lists
