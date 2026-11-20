module

public import Ecma.Prims.Lists
public import Ecma.Prims.Date

@[expose] public section

/-!
# Notation primitives: mathematical values, Numbers and BigInts

The prose notation of §5.2.6 and §6.1.6 on mathematical values, extended mathematical values,
Numbers and BigInts, the bitwise operations, and the time-related constants of §21.4.1. A words
choice is `Val.choice i`, its alternatives in the template's order.
-/

namespace Ecma.Prims.Numbers

variable {M : Model}

/-- §5.2.6, §6.1.6.1 "x is finite": an extended mathematical value or a Number that is neither ±∞ nor NaN; a BigInt, an integer, always (§7.2.13 IsLooselyEqual step 13). -/
def isFinite : List (Val M) → Run M (Val M)
  | [.math _] => Run.pure (.bool true)
  | [.big _] => Run.pure (.bool true)
  | [.posInf] => Run.pure (.bool false)
  | [.negInf] => Run.pure (.bool false)
  | [.num n] => Run.pure (.bool (match M.numView n with
    | .nan => false
    | .posInf => false
    | .negInf => false
    | _ => true))
  | _ => Run.stop .sortError

/-- Whether a Number is +0𝔽 (false) or -0𝔽 (true). -/
def isZero (neg : Bool) (n : M.Num) : Bool :=
  match M.numView n with
  | .posZero => !neg
  | .negZero => neg
  | _ => false

/-- §5.2.6 `a ≤ b` between Numbers of an interval: -0𝔽 below +0𝔽, NaN in no relation. -/
def numLe (a b : M.Num) : Bool :=
  M.numLt a b || (M.numEq a b && !(isZero false a && isZero true b))

/-- §5.2.6 "x is in the inclusive interval from lo to hi": lo ≤ x ≤ hi, of the same numeric type. -/
def inInterval : List (Val M) → Run M (Val M)
  | [.num lo, .num hi, .num x] => Run.pure (.bool (numLe lo x && numLe x hi))
  | [lo, hi, x] => do
    let a ← relOp .le lo x
    let b ← relOp .le x hi
    return .bool (a && b)
  | _ => Run.stop .sortError

/-- §5.2.6 "x is ( even | odd )": an integer that 2 divides, or one that it does not. -/
def parity : List (Val M) → Run M (Val M)
  | [.choice w, .math x] =>
    if M.isInt x then
      let even := M.isInt (M.div x (M.ofNat 2))
      if w == 0 then Run.pure (.bool even)
      else if w == 1 then Run.pure (.bool !even)
      else Run.stop .sortError
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- truncate(x) (§5.2.6): x rounded towards zero. -/
def trunc (x : M.Math) : M.Math :=
  if M.lt x (M.ofNat 0) then M.neg (M.floor (M.neg x)) else M.floor x

/-- §5.2.6 "the remainder of dividing x by y": x - y × truncate(x / y), of x's sign; y non-zero. -/
def remainder : List (Val M) → Run M (Val M)
  | [.math x, .math y] =>
    if M.eq y (M.ofNat 0) then Run.stop .sortError
    else Run.pure (.math (M.sub x (M.mul y (trunc (M.div x y)))))
  | _ => Run.stop .sortError

/-- §5.2.6 "the extended mathematical value of x": ℝ(x) for a finite Number, ±∞ for ±∞𝔽; not for NaN. -/
def xMath : List (Val M) → Run M (Val M)
  | [.num n] => match M.numView n with
    | .nan => Run.stop .sortError
    | .posInf => Run.pure .posInf
    | .negInf => Run.pure .negInf
    | .posZero => Run.pure (.math (M.ofNat 0))
    | .negZero => Run.pure (.math (M.ofNat 0))
    | .finite x => Run.pure (.math x)
  | _ => Run.stop .sortError

/-- §5.2.6 "the negative of x": unary minus by x's type. -/
def negative : List (Val M) → Run M (Val M)
  | [x] => unOp .neg x
  | _ => Run.stop .sortError

/-- §5.2.6, §6.1.6.1 "the Number value for x", 𝔽(x): an extended mathematical value as a Number. -/
def numberFor : List (Val M) → Run M (Val M)
  | [.math x] => Run.pure (.num (if M.eq x (M.ofNat 0) then M.numZero false else M.numOf x))
  | [.posInf] => Run.pure (.num (M.numInf false))
  | [.negInf] => Run.pure (.num (M.numInf true))
  | _ => Run.stop .sortError

/-- §5.2.6 "the BigInt value for x", ℤ(x): an integer as a BigInt. -/
def bigIntFor : List (Val M) → Run M (Val M)
  | [.math x] => bigFor x
  | _ => Run.stop .sortError

/-- "the (Number | BigInt) value that corresponds to x": selector 0 is 𝔽(x), or x itself for a
Number (an IEEE 754-2019 value decoded as a Number), 1 is ℤ(x). -/
def valueFor : List (Val M) → Run M (Val M)
  | [.choice 0, .num x] => Run.pure (.num x)
  | [.choice 0, x] => numberFor [x]
  | [.choice 1, x] => bigIntFor [x]
  | vs => numberFor vs

/-- The bit operation: 0 AND, 1 XOR, 2 OR. -/
def bitOp (op : Nat) (a b : Bool) : Bool :=
  if op == 0 then a && b else if op == 1 then a != b else a || b

/-- floor(x / 2): an integer shifted one bit right. -/
def half (x : M.Math) : M.Math := M.floor (M.div x (M.ofNat 2))

/-- Whether an integer's two's complement bit string is all ones or all zeros from bit 0 on. -/
def isSignOnly (x : M.Math) : Bool := M.eq x (M.ofNat 0) || M.eq x (M.neg (M.ofNat 1))

/-- The integer whose bit string is the bit everywhere: -1 or 0. -/
def ofSign (b : Bool) : M.Math := if b then M.neg (M.ofNat 1) else M.ofNat 0

/-- The bitwise operation on two integers in two's complement, bit 0 first; `none` past `k` bits. -/
def bits (op : Nat) : Nat → M.Math → M.Math → Option M.Math
  | 0, x, y =>
    if isSignOnly x && isSignOnly y then
      some (ofSign (bitOp op (!M.eq x (M.ofNat 0)) (!M.eq y (M.ofNat 0))))
    else none
  | k + 1, x, y =>
    if isSignOnly x && isSignOnly y then
      some (ofSign (bitOp op (!M.eq x (M.ofNat 0)) (!M.eq y (M.ofNat 0))))
    else
      let lo := bitOp op (!M.eq (M.sub x (M.mul (M.ofNat 2) (half x))) (M.ofNat 0))
        (!M.eq (M.sub y (M.mul (M.ofNat 2) (half y))) (M.ofNat 0))
      (bits op k (half x) (half y)).map fun r =>
        M.add (M.mul (M.ofNat 2) r) (if lo then M.ofNat 1 else M.ofNat 0)

/-- A 32-bit two's complement bit string, as the integer of its unsigned binary representation: an integer from 0
to 2^32 - 1. -/
def isBits32 (x : M.Math) : Bool := M.isInt x && !M.lt x (M.ofNat 0) && M.lt x (M.ofNat (2 ^ 32))

/-- §6.1.6.1, §25.4 "the result of applying the bitwise ( AND | XOR | OR ) operation to x and y": bytes (§25.4's
byte values) or 32-bit bit strings (the integers of their unsigned representation), bit by bit. -/
def bitwise : List (Val M) → Run M (Val M)
  | [.choice op, .math x, .math y] =>
    if op ≤ 2 && isBits32 x && isBits32 y then
      match bits op 32 x y with
      | some r => Run.pure (.math r)
      | none => Run.stop .sortError
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §5.2.6 π: the ratio of a circle's circumference to its diameter. -/
def pi : List (Val M) → Run M (Val M)
  | [] => Run.pure (.math M.pi)
  | _ => Run.stop .sortError

/-- §5.2.6 ln(x), log10(x), log2(x): `Model.fn` at `f`, for x > 0. -/
def logOf (f : MathFn) : List (Val M) → Run M (Val M)
  | [.math x] => if M.lt (M.ofNat 0) x then Run.pure (.math (M.fn f x)) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- The functions of "the ( cosine | sine | … ) of x", in the template's order; `none` the square root. -/
def mathFnOf : Nat → Option (Option MathFn)
  | 0 => some (some .cos)
  | 1 => some (some .sin)
  | 2 => some (some .tan)
  | 3 => some (some .cbrt)
  | 4 => some none
  | 5 => some (some .exp)
  | 6 => some (some .cosh)
  | 7 => some (some .sinh)
  | 8 => some (some .tanh)
  | 9 => some (some .acos)
  | 10 => some (some .asin)
  | 11 => some (some .atan)
  | 12 => some (some .acosh)
  | 13 => some (some .asinh)
  | 14 => some (some .atanh)
  | _ => none

/-- Whether x is in the domain of `f` (`none`: the square root) as a mathematical value. -/
def mathFnDom (f : Option MathFn) (x : M.Math) : Bool :=
  let one := M.ofNat 1
  match f with
  | none => !M.lt x (M.ofNat 0)
  | some .acos | some .asin => !M.lt x (M.neg one) && !M.lt one x
  | some .acosh => !M.lt x one
  | some .atanh => M.lt (M.neg one) x && M.lt x one
  | some _ => true

/-- §21.3 "the ( cosine | sine | … ) of x": `Model.fn`, or `Model.sqrt` for the square root, on
the function's domain. -/
def mathFn : List (Val M) → Run M (Val M)
  | [.choice w, .math x] => match mathFnOf w with
    | some f => if !mathFnDom f x then Run.stop .sortError else match f with
      | some f => Run.pure (.math (M.fn f x))
      | none => Run.pure (.math (M.sqrt x))
    | none => Run.stop .sortError
  | _ => Run.stop .sortError

/-- 10^n. -/
def tenTo (n : Nat) : M.Math := M.pow (M.ofNat 10) (M.ofNat n)

/-- §21.4.1 the time-related constants, HoursPerDay to MinEpochNanoseconds, in the clause's order. -/
def timeConst : List (Val M) → Run M (Val M)
  | [.choice w] => match w with
    | 0 => Run.pure (.math (M.ofNat 24))
    | 1 => Run.pure (.math (M.ofNat 60))
    | 2 => Run.pure (.math (M.ofNat 60))
    | 3 => Run.pure (.math (M.ofNat 1000))
    | 4 => Run.pure (.math (M.ofNat 60000))
    | 5 => Run.pure (.math (M.ofNat 3600000))
    | 6 => Run.pure (.math (M.ofNat 86400000))
    | 7 => Run.pure (.math (M.mul (tenTo 6) (M.ofNat 86400000)))
    | 8 => Run.pure (.math (tenTo 9))
    | 9 => Run.pure (.math (tenTo 6))
    | 10 => Run.pure (.math (tenTo 3))
    | 11 => Run.pure (.math (M.mul (tenTo 14) (M.ofNat 86400000)))
    | 12 => Run.pure (.math (M.neg (M.mul (tenTo 14) (M.ofNat 86400000))))
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The relation of a words choice ( `<` | ≤ ). -/
def chainRel : Nat → Option RelOp
  | 0 => some .lt
  | 1 => some .le
  | _ => none

/-- §5.2.6 "a ( < | ≤ ) b ( < | ≤ ) c": both comparisons, by the operands' type. -/
def chain : List (Val M) → Run M (Val M)
  | [a, .choice o1, b, .choice o2, c] => match chainRel o1, chainRel o2 with
    | some r1, some r2 => do
      let x ← relOp r1 a b
      let y ← relOp r2 b c
      return .bool (x && y)
    | _, _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.6.1.20 step 5: NumberDigitsExponent(x, radix) (i = 0), NumberDigitsCount(x, radix) (i = 1),
NumberDigitsSignificand(x, radix) (i = 2): the step's n, k and s for a finite Number x > +0𝔽 and an integer radix
from 2 to 36, the model's `numDigits`. -/
def numberDigits (i : Nat) : List (Val M) → Run M (Val M)
  | [.num x, .math r] => match M.numView x with
    | .finite m =>
      if M.lt (M.ofNat 0) m && M.isInt r && !M.lt r (M.ofNat 2) && !M.lt (M.ofNat 36) r then
        let d := M.numDigits x r
        Run.pure (.math (if i == 0 then d.1 else if i == 1 then M.ofNat d.2.1 else d.2.2))
      else Run.stop .sortError
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- DecimalExponent(x): the integer e with 10^e ≤ x < 10^(e+1), for x > 0, the model's `decExp`: the place of the
first significant digit of x's decimal representation. -/
def decimalExponent : List (Val M) → Run M (Val M)
  | [.math x] => if M.lt (M.ofNat 0) x then Run.pure (.math (M.decExp x)) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- The family's primitives by id; `none` for an id outside it. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pIsFinite then some (isFinite vs)
  else if p == Known.pInInterval then some (inInterval vs)
  else if p == Known.pParity then some (parity vs)
  else if p == Known.pRemainder then some (remainder vs)
  else if p == Known.pXMath then some (xMath vs)
  else if p == Known.pNegative then some (negative vs)
  else if p == Known.pNumberFor then some (valueFor vs)
  else if p == Known.pBigIntFor then some (bigIntFor vs)
  else if p == Known.pBitwise then some (bitwise vs)
  else if p == Known.pPi then some (pi vs)
  else if p == Known.pLn then some (logOf .ln vs)
  else if p == Known.pLog10 then some (logOf .log10 vs)
  else if p == Known.pLog2 then some (logOf .log2 vs)
  else if p == Known.pMathFn then some (mathFn vs)
  else if p == Known.pTimeConst then some (timeConst vs)
  else if p == Known.pChain then some (chain vs)
  else if p == Known.pYearFromTimeOf then some (Date.yearFromTime vs)
  else if p == Known.pFirstDayOf then some (Date.firstDayOf vs)
  else if p == Known.pNumberDigitsExponent then some (numberDigits 0 vs)
  else if p == Known.pNumberDigitsCount then some (numberDigits 1 vs)
  else if p == Known.pNumberDigitsSignificand then some (numberDigits 2 vs)
  else if p == Known.pDecimalExponent then some (decimalExponent vs)
  else if p == Known.pIntToRadix then
    some <| match vs with
      | [.math n, .math r] =>
        if M.isInt n && !M.lt n (M.ofNat 0) && M.isInt r && !M.lt r (M.ofNat 2) && !M.lt (M.ofNat 36) r then
          Run.pure (.str (M.intToRadix n r))
        else Run.stop .sortError
      | _ => Run.stop .sortError
  else none

end Ecma.Prims.Numbers
