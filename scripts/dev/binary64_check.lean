import Engine.Model.Binary64
open Engine.Binary64

/-! The machine's binary64 operations against their definitions (`Binary64.add`, `mul`, `div`: the exact result
rounded): special operands in every pair, then pseudo-random patterns. `lake env lean scripts/dev/binary64_check.lean` -/

-- The definitions, not their compiled replacements: unfolded here by hand.
def addDef (a b : BitVec 64) : BitVec 64 :=
  if isNaN a || isNaN b then qNaN
  else if isInfinite a then (if isInfinite b && sign a != sign b then qNaN else a)
  else if isInfinite b then b
  else if isNegZero a && isNegZero b then negZero
  else ofRat (toRat a + toRat b)
def mulDef (a b : BitVec 64) : BitVec 64 :=
  let s := sign a != sign b
  if isNaN a || isNaN b then qNaN
  else if isInfinite a || isInfinite b then (if isZero a || isZero b then qNaN else infinity s)
  else if isZero a || isZero b then zero s
  else ofRat (toRat a * toRat b)
def divDef (a b : BitVec 64) : BitVec 64 :=
  let s := sign a != sign b
  if isNaN a || isNaN b then qNaN
  else if isInfinite a then (if isInfinite b then qNaN else infinity s)
  else if isInfinite b then zero s
  else if isZero b then (if isZero a then qNaN else infinity s)
  else if isZero a then zero s
  else ofRat (toRat a / toRat b)

def specials : List (BitVec 64) := [0x0, 0x8000000000000000, 0x1, 0x8000000000000001, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
  0x3FF0000000000000, 0xBFF0000000000000, 0x3FF0000000000001, 0x3FB999999999999A, 0x3FC999999999999A, 0x3FD3333333333333,
  0x4340000000000000, 0x433FFFFFFFFFFFFF, 0x7FEFFFFFFFFFFFFF, 0xFFEFFFFFFFFFFFFF, 0x7FF0000000000000, 0xFFF0000000000000,
  0x7FF8000000000000, 0x7FF0000000000001, 0xFFF8000000000123, 0x3CA0000000000000, 0x3FE0000000000000, 0x4008000000000000]

def next (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def main : IO Unit := do
  let mut bad := 0
  let mut n := 0
  let test := fun (a b : BitVec 64) =>
    (addHw a b == addDef a b, mulHw a b == mulDef a b, divHw a b == divDef a b)
  for a in specials do
    for b in specials do
      n := n + 1
      let (x, y, z) := test a b
      unless x && y && z do
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"differs at {a.toNat} {b.toNat}: add {x} mul {y} div {z}"
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  for i in [0:20000] do
    s := next s; let a0 := s
    s := next s; let b0 := s
    -- one in four: exponents near each other, where rounding is tested hardest
    let b1 := if i % 4 == 0 then (a0 &&& 0xFFF0000000000000) ||| (b0 &&& 0x000FFFFFFFFFFFFF) else b0
    let a := BitVec.ofNat 64 a0.toNat
    let b := BitVec.ofNat 64 b1.toNat
    n := n + 1
    let (x, y, z) := test a b
    unless x && y && z do
      bad := bad + 1
      if bad ≤ 5 then IO.println s!"differs at {a.toNat} {b.toNat}: add {x} mul {y} div {z}"
  IO.println s!"{n} operand pairs, {bad} differ"

#eval main
