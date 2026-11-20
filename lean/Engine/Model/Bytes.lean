module

public import Engine.Model.Bare

@[expose] public section

/-! # Byte sequences (`ByteArray`) for `Engine.Impl` -/

namespace Engine.Model

def fillLoop : Nat → UInt8 → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, b, acc => fillLoop n b (acc.push b)

def byte? (v : MathVal) : Option UInt8 :=
  match v with
  | .int i => if 0 ≤ i ∧ i < 256 then some (UInt8.ofNat i.toNat) else none
  | .frac _ _ => none

/-- A Data Block of `n` zero bytes (empty if `n` is not a non-negative integer). -/
def bytesZero (n : MathVal) : ByteArray :=
  match MathVal.idx n with
  | some k => fillLoop k 0 (ByteArray.emptyWithCapacity k)
  | none => ByteArray.empty

def bytesLen (bs : ByteArray) : MathVal :=
  .int bs.size

def bytesGet (bs : ByteArray) (i : MathVal) : Option MathVal :=
  (MathVal.idx i).bind fun k =>
    if k < bs.size then some (.int (bs.get! k).toNat) else none

def bytesSet (bs : ByteArray) (i v : MathVal) : ByteArray :=
  match MathVal.idx i, byte? v with
  | some k, some b => if k < bs.size then bs.set! k b else bs
  | _, _ => bs

def bytesFill (bs : ByteArray) (v : MathVal) : ByteArray :=
  match byte? v with
  | some b => fillLoop bs.size b (ByteArray.emptyWithCapacity bs.size)
  | none => bs

def bytesResize (bs : ByteArray) (n : Nat) : ByteArray :=
  let k := min bs.size n
  fillLoop (n - k) 0 (bs.extract 0 k)

end Engine.Model
