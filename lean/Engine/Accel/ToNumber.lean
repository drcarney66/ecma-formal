module

public import Ecma.State
public import Engine.Model
public import Engine.Accel.ToString

@[expose] public section

/-!
# Numeric index and conversion shortcuts at Impl

* `toNumEntry`: `ToNumber` on Numbers, `undefined`, `null`, and Booleans.
* `cnisEntry`: `CanonicalNumericIndexString` on `"-0"`.
* `roundDecMVEntry`: `@formal-rounddecimalmv(m, 0)` on non-negative safe integers `0 ≤ m < 2^53`.
* `snvSdo`: `StringNumericValue` SDO on plain decimal integer `|StringNumericLiteral|` Parse Nodes `< 2^53`.
-/

namespace Engine.Accel

open Ecma Engine.Model

/-- Canonical binary64 Number for a non-negative integer `0 ≤ n < 2^53`. -/
def numOfSafeNat (n : Nat) : F.Num :=
  if n == 0 then F.numZero false else F.numOf (.int n)

/-- `ToNumber(arg)` on primitive non-String, non-Symbol, non-BigInt values. -/
def toNumEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.num x] =>
    some (always (pure (.comp Known.eNormal (.num x) (.enum Known.eEmpty))))
  | [.undefined] =>
    some (always (pure (.comp Known.eNormal (.num F.numNaN) (.enum Known.eEmpty))))
  | [.null] =>
    some (always (pure (.comp Known.eNormal (.num (F.numZero false)) (.enum Known.eEmpty))))
  | [.bool false] =>
    some (always (pure (.comp Known.eNormal (.num (F.numZero false)) (.enum Known.eEmpty))))
  | [.bool true] =>
    some (always (pure (.comp Known.eNormal (.num (F.numOf (.int 1))) (.enum Known.eEmpty))))
  | _ => none

/-- `CanonicalNumericIndexString(arg)` fast path on `"-0"`. -/
def cnisEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.str s] =>
    if s == #[45, 48] then some (always (pure (.num (F.numZero true)))) else none
  | _ => none

/-- `@formal-rounddecimalmv(m, 0)` on non-negative safe integers `0 ≤ m < 2^53`. -/
def roundDecMVEntry : List (Val F) → Option (Run F (Option (Val F)))
  | [.math (.int m), .math (.int 0)] =>
    if 0 ≤ m ∧ m < 2 ^ 53 then
      some (always (pure (.num (numOfSafeNat m.toNat))))
    else none
  | _ => none

/-- Required child `k` (occurrence 0) of `nd`. -/
def childNode (nd : F.Node) (k : NtId) : Option F.Node :=
  match F.nodeChild nd k 0 with
  | some (some c) => some c
  | _ => none

/-- `MV` of a `DecimalDigit :: '0' .. '9'` Parse Node. -/
def decDigitVal (nd : F.Node) : Option Nat :=
  let p := F.nodeProd nd
  if p == Known.prodDecDigit0 then some 0
  else if p == Known.prodDecDigit1 then some 1
  else if p == Known.prodDecDigit2 then some 2
  else if p == Known.prodDecDigit3 then some 3
  else if p == Known.prodDecDigit4 then some 4
  else if p == Known.prodDecDigit5 then some 5
  else if p == Known.prodDecDigit6 then some 6
  else if p == Known.prodDecDigit7 then some 7
  else if p == Known.prodDecDigit8 then some 8
  else if p == Known.prodDecDigit9 then some 9
  else none

/-- `MV` of a `[~Sep]` `DecimalDigits` spine of depth at most `fuel`. -/
def decDigitsVal : Nat → F.Node → Option Nat
  | 0, _ => none
  | fuel + 1, nd =>
    let p := F.nodeProd nd
    if p == Known.prodDecDigits1 then do
      let d ← childNode nd Known.ntDecimalDigit
      decDigitVal d
    else if p == Known.prodDecDigitsStep then do
      let pre ← childNode nd Known.ntDecimalDigits
      let d ← childNode nd Known.ntDecimalDigit
      let v ← decDigitsVal fuel pre
      let dv ← decDigitVal d
      some (v * 10 + dv)
    else none

/-- Plain unsigned integer `StringNumericLiteral` value `< 2^53` (at most 16 digits, no whitespace, sign, dot, or exponent). -/
def snvPlainNat (nd : F.Node) : Option Nat := do
  guard (F.nodeProd nd == Known.prodStrNumLit)
  let n1 ← childNode nd Known.ntStrNumericLiteral
  guard (F.nodeProd n1 == Known.prodStrNumDec)
  let n2 ← childNode n1 Known.ntStrDecimalLiteral
  guard (F.nodeProd n2 == Known.prodStrDecUnsigned)
  let n3 ← childNode n2 Known.ntStrUnsignedDecimalLiteral
  guard (F.nodeProd n3 == Known.prodStrUnsignedDigits)
  let ds ← childNode n3 Known.ntDecimalDigits
  guard (F.nodeChild n3 Known.ntExponentPart 0 == some none)
  let v ← decDigitsVal 16 ds
  guard (v < 2 ^ 53)
  some v

/-- `StringNumericValue` SDO shortcut on plain integer `StringNumericLiteral` Parse Nodes `< 2^53`. -/
def snvSdo (nd : F.Node) (vs : List (Val F)) : Option (Run F (Val F)) :=
  match vs with
  | [] => (snvPlainNat nd).map fun v => Run.pure (.num (numOfSafeNat v))
  | _ => none

end Engine.Accel
