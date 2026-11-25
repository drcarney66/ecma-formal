module

public import Ecma.State
public import Ecma.Machine.Code
public import Engine.Model
public import Engine.Accel.ToString
public import Engine.Accel.StringScan
public import Std.Data.HashSet
public import Std.Data.HashMap

@[expose] public section

/-!
# Accelerated algorithms at Impl, by name

`byName` gives, for some algorithms by their name, a computation of their result from the call's
arguments. An entry answers `none` for arguments it does not cover, and its run may decline (`.ok
none`) in a state it does not cover: in either case the algorithm's meaning runs, from the state the
run left.

* Number::toString: `toStringEntry` (`Ecma.Engine.AccelToString`).
* sort-WriteSharedMemory-event: the Record's kind, which SingleAgentReadBytes's scan asks of each
  event.
* StringToCodePoints and GetStringIndex: one scan of the String (`Ecma.Engine.AccelStringScan`), with
  CodePointAt's Records.
* The sparse HasProperty loops (`skipRun`, at `hasPropLoop`'s steps): the rounds of `Repeat, while`
  over `HasProperty(O, ! ToString(𝔽(k)))` whose k is no key on O's ordinary prototype chain.

Accelerator debt: each accelerated call equals the machine's; `skipRun`'s rounds equal the machine's
(Number::toString's String at integers, the HasProperty miss on an ordinary chain).
-/

namespace Engine.Accel

open Ecma Engine.Model

/-! ## WriteSharedMemory event -/

/-- The Record sort WriteSharedMemory. -/
def sWrite : SortId := Known.sWriteSharedMemory

/-- `v is a WriteSharedMemory event`: a Record of the sort WriteSharedMemory (no sort lies below it). -/
def isWrite (v : Val F) : Run F (Val F) := fun s => match v with
  | .ref a => match F.heapGet s.heap a with
    | some (.record k _) | some (.env k _ _) => .ok (.bool (k == sWrite)) s
    | some _ => .ok (.bool false) s
    | none => .stop .sortError
  | _ => .ok (.bool false) s

def isWriteEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.unbound] => none
  | [v] => some (always (isWrite v))
  | _ => none

/-! ## The sparse HasProperty loops -/

/-- The slots of a `Repeat, while` HasProperty loop: the index, its bound (`none`: `k ≥ 0`, descending), the object,
the key and whether the object has it. -/
structure LoopSlots where
  k : Slot
  bound : Option Slot
  o : Slot
  pk : Slot
  kp : Slot
  deriving BEq, DecidableEq, Repr

/-- The loop counts down. -/
def LoopSlots.desc (m : LoopSlots) : Bool := m.bound.isNone

/-- The slots of lowered `Repeat, while k < len` (or `k ≥ 0`) over `Let pk be ! ToString(𝔽(k))`, `Let kp be ? HasProperty(o,
pk)`, `If kp is true, then …` and `Set k to k + 1` (or `k - 1`), its variables pairwise distinct; `none` for other loops. -/
def hasPropLoop : List Nat → Ecma.Machine.Op → Ecma.Machine.Code → Option LoopSlots
  | p, t, [.site p1, .let_ pk (.leaf .bang [.call (.alg ⟨cToStr, iToStr⟩) [.call (.prim prF) [.var k1]]]),
      .site p2, .let_ kp (.leaf .q [.call (.alg ⟨cHasProp, iHasProp⟩) [.var o, .var pk1]]),
      .site p3, .br (.bind (.var kp1) (.and [.leaf (.isVal false false) [.bound, .const (.val .true)]])) _ [],
      .site p4, .let_ k2 (.leaf (.bin op) [.var k3, .const (.math .none (.num (.dec 1)))])] =>
    let bound : Option (Option Slot) := match t, op with
      | .leaf (.rel .lt) [.var k0, .var len], .add => if k0 == k1 then some (some len) else none
      | .leaf (.rel .ge) [.var k0, .const (.math .none (.num (.dec 0)))], .sub => if k0 == k1 then some none else none
      | _, _ => none
    bound.bind fun b =>
      let xs := [k1, o, pk, kp] ++ b.toList
      if cToStr == Known.cToString && iToStr == 0 && prF == Known.pF &&
          cHasProp == Known.cHasProperty && iHasProp == 0 &&
          p1 == 1 :: p && p2 == 2 :: p && p3 == 3 :: p && p4 == 4 :: p &&
          k1 == k2 && k1 == k3 && pk == pk1 && kp == kp1 && xs.eraseDups.length == xs.length then
        some { k := k1, bound := b, o, pk, kp }
      else none
  | _, _, _ => none

/-- The most objects a skip walks on the prototype chain. -/
def chainLimit : Nat := 64

/-- The indices a skip probes one by one before it scans the chain's keys. -/
def probeLimit : Nat := 64

/-- The most property keys on the chain a skip scans. -/
def keyLimit : Nat := 4096

/-- `[[Prototype]]` and the internal methods a HasProperty miss calls: `[[HasProperty]]`,
`[[GetOwnProperty]]`, `[[GetPrototypeOf]]` and their ordinary definitions. -/
def fProto : FieldId := Known.fPrototype
def ordinaryMethods : List (FieldId × AlgId) :=
  [(Known.fHasProperty, ⟨Known.cOrdMethodHasProperty, 0⟩),
   (Known.fGetOwnProperty, ⟨Known.cOrdMethodGetOwnProperty, 0⟩),
   (Known.fGetPrototypeOf, ⟨Known.cOrdMethodGetPrototypeOf, 0⟩)]

/-- The own properties of each object on the chain from `a`, if it has at most `n` objects, each ordinary in
`ordinaryMethods`, its [[Prototype]] an object or null. -/
def ordChain (s : State F) : Nat → F.Addr → Option (List (F.Props (Val F)))
  | 0, _ => none
  | n + 1, a => match F.heapGet s.heap a with
    | some (.object sl ps) =>
      if ordinaryMethods.all fun (f, g) => match F.recGet sl f with
          | some (.alg h) => h == g
          | _ => false then
        match F.recGet sl fProto with
        | some .null => some [ps]
        | some (.obj p) => (ordChain s n p).map (ps :: ·)
        | _ => none
      else none
    | _ => none

/-- The key `ToString(𝔽(i))` of an integer 0 ≤ i < 2^53. -/
def indexKey (i : Nat) : F.Str ⊕ F.Sym := .inl (F.strLit (toString i))

/-- Some object of the chain has the key `ToString(𝔽(i))`. -/
def chainHas (ch : List (F.Props (Val F))) (i : Nat) : Bool := ch.any fun ps => (F.propsGet ps (indexKey i)).isSome

/-- The number of an object's own properties. -/
def propsSize (ps : F.Props (Val F)) : Nat := (show Engine.Model.WMap (Array UInt16 ⊕ (Nat × Option (Array UInt16)))
  (Val F) from ps).index.size

/-- The first `d < n` at which the chain has `ToString(𝔽(i ± d))` (`desc`: `-`), or `n`. -/
def probe (ch : List (F.Props (Val F))) (desc : Bool) (i : Nat) (n : Nat) : Nat :=
  ((List.range n).find? fun d => chainHas ch (if desc then i - d else i + d)).getD n

/-- An object's own property keys, as its hash index holds them. -/
def indexKeys (ps : F.Props (Val F)) : List (F.Str ⊕ F.Sym) :=
  (show Engine.Model.WMap (Array UInt16 ⊕ (Nat × Option (Array UInt16))) (Val F) from ps).index.keys

/-- The distance from `i` to the nearest index key on the chain past `i ± p` (`desc`: below), if any. -/
def nearestKey (ch : List (F.Props (Val F))) (desc : Bool) (i p : Nat) : Option Nat :=
  ch.foldl (fun acc ps => (indexKeys ps).foldl (fun acc k => match indexOf (M := F) k with
    | some (.int j) =>
      let d := if desc then (i : Int) - j else j - (i : Int)
      if p < d then some (match acc with
        | some e => min e d.toNat
        | none => d.toNat) else acc
    | _ => acc) acc) none

/-- The rounds from `k = i` with no key `ToString(𝔽(k))` on the ordinary chain of the object in slot `o`: at most `left`
(the loop's rounds left) and while the condition holds, up to the next index key. It runs them: `k` past them, `pk`
the last one's key and `kp` false. `none` where a slot, the chain or the condition at `i` does not fit, or `i` has a
key. -/
def skipRun (m : LoopSlots) (left : Option Nat) (sl : Array (Val F)) (s : State F) :
    Option (Run F (Nat × List (Slot × Val F))) := do
  let .math (.int i) ← sl[m.k]? | none
  let .obj a ← sl[m.o]? | none
  guard (0 ≤ i && i < 2 ^ 53 && m.pk < sl.size && m.kp < sl.size)
  let i := i.toNat
  let span ← match m.bound with
    | some b => match sl[b]? with
      | some (.math (.int len)) => some (min len (2 ^ 53) - i).toNat
      | _ => none
    | none => some (i + 1)
  let lim := match left with
    | some l => min span l
    | none => span
  guard (0 < lim)
  let ch ← ordChain s chainLimit a
  let n := min (probeLimit + 1) lim
  let d := probe ch m.desc i n
  guard (0 < d)
  let g := if d < n || n == lim then d
    else if (ch.map propsSize).sum ≤ keyLimit then min lim ((nearestKey ch m.desc i probeLimit).getD lim)
    else n
  let last := if m.desc then i - (g - 1) else i + (g - 1)
  some fun st => .ok (g, [(m.k, .math (.int (if m.desc then (i : Int) - g else i + g))),
      (m.pk, .str (F.strLit (toString last))), (m.kp, .bool false)]) st

/-! ## The table -/

abbrev Entry := List (Val F) → Option (Run F (Option (Val F)))

end Engine.Accel
