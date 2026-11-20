module

public import Engine.Model.Bare

@[expose] public section

/-! # String repetition and radix conversion (`Engine.Impl`) -/

namespace Engine.Model

def strRepeatAux (s : Array UInt16) : Nat → Array UInt16 → Array UInt16
  | 0, acc => acc
  | k + 1, acc => strRepeatAux s k (acc ++ s)

/-- `n` concatenated copies of `s` (empty immediately when `s` is empty). -/
def strRepeat (n : MathVal) (s : Array UInt16) : Array UInt16 :=
  if s.isEmpty then #[]
  else match MathVal.idx n with
    | some k => strRepeatAux s k (Array.mkEmpty (k * s.size))
    | none => #[]

@[inline] def radixDigit (d : Nat) : UInt16 :=
  if d < 10 then (48 + d).toUInt16 else (87 + d).toUInt16

def radixLoop (r : Nat) (hr : 2 ≤ r) (n : Nat) (acc : List UInt16) : List UInt16 :=
  if h : n < r then radixDigit n :: acc
  else
    have : n / r < n := Nat.div_lt_self (by omega) (by omega)
    radixLoop r hr (n / r) (radixDigit (n % r) :: acc)
termination_by n

/-- Non-negative integer `n` formatted in radix `r` (`2 ≤ r ≤ 36`). -/
def intToRadix (n r : MathVal) : Array UInt16 :=
  match MathVal.idx n, MathVal.idx r with
  | some k, some b =>
    if h : 2 ≤ b ∧ b ≤ 36 then (radixLoop b h.1 k []).toArray else #[]
  | _, _ => #[]

end Engine.Model
