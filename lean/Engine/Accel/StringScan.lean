module

public import Ecma.State
public import Engine.Model
public import Engine.Accel.ToString

@[expose] public section

/-!
# The String scans of the RegExp algorithms at Impl

StringToCodePoints(S) and GetStringIndex(S, i) by one native scan of S's code units (`cpAt` is CodePointAt's
steps), each making the cells the machine makes: StringToCodePoints the List of the code points, then one
CodePointAt Record per code point; GetStringIndex one Record per code point before the i-th. Each declines for a
String of more than `scanLimit` code units.
-/

namespace Engine.Accel

open Ecma Engine.Model

/-- The heap as an Array. -/
abbrev heapArr (st : State F) : Array (Cell F) := st.heap

/-- The most code units a String scan entry walks. -/
def scanLimit : Nat := 0x1000000

/-- CodePointAt(s, p)'s [[CodePoint]], [[CodeUnitCount]] and [[IsUnpairedSurrogate]]. -/
def cpAt (s : Array UInt16) (p : Nat) : Int × Nat × Bool :=
  let first : Int := (s[p]?.getD 0).toNat
  if first < 0xD800 ∨ 0xDFFF < first then (first, 1, false)
  else if 0xDC00 ≤ first ∨ p + 1 = s.size then (first, 1, true)
  else
    let second : Int := (s[p + 1]?.getD 0).toNat
    if second < 0xDC00 ∨ 0xDFFF < second then (first, 1, true)
    else ((first - 0xD800) * 0x400 + (second - 0xDC00) + 0x10000, 2, false)

/-- The Record CodePointAt returns, of the sort Record (8). -/
def cpRec (t : Int × Nat × Bool) : Cell F :=
  .record 8 (F.recSet (F.recSet (F.recSet F.recEmpty 150 (.math (.int t.1))) 51 (.math (.int t.2.1))) 50
    (.bool t.2.2))

/-- StringToCodePoints's loop from code unit p, at most k rounds: the code points and the Records pushed. -/
def scanCps (s : Array UInt16) : Nat → Nat → Array (Val F) → Array (Cell F) → Array (Val F) × Array (Cell F)
  | 0, _, cs, rs => (cs, rs)
  | k + 1, p, cs, rs =>
    if p < s.size then
      let t := cpAt s p
      scanCps s k (p + t.2.1) (cs.push (.math (.int t.1))) (rs.push (cpRec t))
    else (cs, rs)

/-- StringToCodePoints(s): a new List of its code points, then CodePointAt's Records. -/
def stcpRun (s : Array UInt16) : Run F (Val F) := fun st =>
  let r := scanCps s s.size 0 #[] #[]
  .ok (.ref (heapArr st).size) { st with heap := ((heapArr st).push (.list r.1 0) ++ r.2 : Array (Cell F)) }

def stcpEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.str s] => if s.size ≤ scanLimit then some (always (stcpRun s)) else none
  | _ => none

/-- GetStringIndex's loop from code unit p and code point c, at most k rounds: the code unit index and the
Records pushed. -/
def scanIdx (s : Array UInt16) (i : Int) : Nat → Nat → Nat → Array (Cell F) → Nat × Array (Cell F)
  | 0, _, _, rs => (s.size, rs)
  | k + 1, p, c, rs =>
    if p < s.size then
      if (c : Int) = i then (p, rs)
      else
        let t := cpAt s p
        scanIdx s i k (p + t.2.1) (c + 1) (rs.push (cpRec t))
    else (s.size, rs)

/-- GetStringIndex(s, i): 0 for the empty String, else the index the loop returns, and its Records. -/
def gsiRun (s : Array UInt16) (i : Int) : Run F (Val F) := fun st =>
  if s.size = 0 then .ok (.math (.int 0)) st
  else
    let r := scanIdx s i s.size 0 0 #[]
    .ok (.math (.int r.1)) { st with heap := ((heapArr st) ++ r.2 : Array (Cell F)) }

def gsiEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.str s, .math (.int i)] => if s.size ≤ scanLimit then some (always (gsiRun s i)) else none
  | _ => none

end Engine.Accel
