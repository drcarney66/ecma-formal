module

public import Ecma.Host.Laws.Basic

@[expose] public section

/-!
# The laws of the values the implementation chooses

Implementation-approximated values, implementation-defined choices, Math.random, and the maximum BigInt size.
-/

namespace Ecma

variable {M : Model}

/-- `n` is a Number with positive sign, greater than or equal to +0 and less than 1. -/
def unitNum (n : M.Num) : Prop :=
  M.numView n = .posZero ∨
    ∃ m, M.numView n = .finite m ∧ M.lt (M.ofNat 0) m = true ∧ M.lt m (M.ofNat 1) = true

/-- The laws of the values the implementation chooses. -/
structure Host.ValueLaws (H : Host M) : Prop where
  /-- sec-math.cbrt step 3, and every "implementation-approximated Number value" of the Math functions:
  "Return an implementation-approximated Number value representing the cube root of ℝ(n)."
  Reading: Approx answers a Number, the state as it was. -/
  approx : H.asks Known.pApprox fun _ _ r => ∃ n, r = .num n
  /-- sec-numeric-types-number-exponentiate step 13:
  "Return an implementation-approximated Number value representing the result of raising ℝ(base) to the ℝ(exponent) power."
  Reading: ApproxPower(_base_, _exponent_) answers a Number, the state as it was. -/
  approxPower : H.asks Known.pApproxPower fun _ _ r => ∃ n, r = .num n
  /-- sec-parseint-string-radix step 11:
  "mathInt may be an implementation-approximated integer representing the integer value denoted by numberString in radix-radixMV notation"
  Reading: ApproxInteger answers an integer, the state as it was. -/
  approxInteger : ∀ (x : M.Math) s r s', H.choice Known.pApproxInteger [.math x] s = .ok r s' →
    s' = s ∧ ∃ m, r = .math m ∧ M.isInt m = true
  /-- No sentence: ECMA-262 sets no maximum size of a BigInt (sec-ecmascript-language-types-bigint-type: "The value
  may be any size and is not limited to a particular bit-width"); the proposed reading of erratum BigIntMaximumSize, a
  proposed normative change, asks the host whether a result would exceed the implementation's maximum.
  Reading: BigIntTooLarge answers a Boolean, the state as it was. -/
  bigIntTooLarge : H.asks Known.pBigIntTooLarge fun _ _ r => ∃ b, r = .bool b
  /-- No sentence: ECMA-262 defines String values up to length 2^53 - 1 and leaves implementations' smaller maximum
  String lengths unspecified; the proposed reading of erratum StringMaximumLength asks the host whether a String
  of length len exceeds the implementation's maximum String length.
  Reading: StringTooLarge answers a Boolean, the state as it was. -/
  stringTooLarge : H.asks Known.pStringTooLarge fun _ _ r => ∃ b, r = .bool b
  /-- sec-roundmvresult step 4, and every "implementation-defined choice of either" two values:
  "Let chosen be an implementation-defined choice of either option1 or option2."
  Reading: HostChoice answers one of its arguments, the state as it was. -/
  hostChoice : H.asks Known.pHostChoice fun vs _ r => r ∈ vs
  /-- sec-math.random:
  "This function returns a Number value with positive sign, greater than or equal to +0𝔽 but strictly less than 1𝔽"
  Reading: Math.random answers such a Number (`unitNum`), never an abrupt completion, the state as it was. -/
  mathRandom : ∀ c xs s r s', Gen.clauses[c]? = some "sec-math.random" → H.answers c xs s r s' →
    s' = s ∧ ∃ n, r = .num n ∧ unitNum n

end Ecma
