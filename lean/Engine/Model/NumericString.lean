module

public import Engine.Model.Bare
public import Engine.Model.CodePrims
public import Engine.Parse.Keys
public import Engine.Parse.Core

@[expose] public section

/-!
# Accelerator: the numeric string grammar's parse

`parse` gives the Parse Node of a StringNumericLiteral or a StringIntegerLiteral (§7.1.4.1,
§7.1.14), the goals StringToNumber and StringToBigInt parse with, by a deterministic descent over
GL's productions of the numeric string grammar and the lexical ones it uses (`[~Sep]`): every
node carries GL's production id with its presence mask, its nonterminal, its span of the input
and its text, and one child entry per written nonterminal item (`none` for an absent optional).
For any other goal it leaves the parse undecided.

<USP> is the instance's (`Engine.Model.usp`).

Every node produced by `parseNumeric` is verified by `Engine.verifyCodeNode` (with fallback to
`Engine.Parse.parse`), so `Ecma.Model.ParseLaws` (`Engine.Claims.parseLaws`) holds unconditionally.
-/

namespace Engine

open Ecma.Grammar Engine.Model
open Ecma (ProdId NtId ParamId)

/-- GL's ids by grammar, left-hand side, written alternative (a `one of` terminal's index) and
presence mask. -/
def ids : Std.HashMap (Nat × Nat × Nat × List Bool) ProdId :=
  Engine.Parse.prods.zipIdx.foldl (init := {}) fun m (o, i) => match o with
    | some p => m.insert (p.grammar.ctorIdx, p.rule.lhs.ctorIdx, p.alt, p.mask) i
    | none => m

/-- The input and the parser invocation. -/
structure Cx where
  cs : Array Nat
  stamp : Nat

/-- The code points from `lo` to `hi`, a view of the input. -/
def Cx.text (cx : Cx) (lo hi : Nat) : Subarray Nat := cx.cs[lo...hi]

/-- The node of `nt`'s alternative `alt` with `mask` over `lo` to `hi`. -/
def Cx.node (cx : Cx) (g : GrammarId) (nt : NT) (alt : Nat) (mask : List Bool) (lo hi : Nat)
    (kids : Array (NtId × Option Node)) : Option Node :=
  (Engine.Parse.prodIdBy g nt alt mask).map fun p => .mk cx.stamp lo hi p nt.ctorIdx [] kids (cx.text lo hi)

/-- §12.2 <USP>: the instance's Space_Separator. -/
def isUSP (c : Nat) : Bool := Engine.Model.usp c

/-- WhiteSpace's alternative for `c`: <TAB>, <VT>, <FF>, <ZWNBSP>, <USP>. -/
def wsAlt (c : Nat) : Option Nat :=
  if c == 0x9 then some 0 else if c == 0xB then some 1 else if c == 0xC then some 2
  else if c == 0xFEFF then some 3 else if isUSP c then some 4 else none

/-- LineTerminator's alternative for `c`: <LF>, <CR>, <LS>, <PS>. -/
def ltAlt (c : Nat) : Option Nat :=
  if c == 0xA then some 0 else if c == 0xD then some 1 else if c == 0x2028 then some 2
  else if c == 0x2029 then some 3 else none

def isStrWhiteSpaceChar (c : Nat) : Bool := (wsAlt c).isSome || (ltAlt c).isSome

/-- StrWhiteSpaceChar at `i`. -/
def Cx.wsChar (cx : Cx) (i : Nat) : Option Node := do
  let c ← cx.cs[i]?
  match wsAlt c, ltAlt c with
  | some a, _ =>
    let w ← cx.node .lexical .WhiteSpace a [] i (i + 1) #[]
    cx.node .numericString .StrWhiteSpaceChar 0 [] i (i + 1) #[(NT.WhiteSpace.ctorIdx, some w)]
  | none, some a =>
    let l ← cx.node .lexical .LineTerminator a [] i (i + 1) #[]
    cx.node .numericString .StrWhiteSpaceChar 1 [] i (i + 1) #[(NT.LineTerminator.ctorIdx, some l)]
  | none, none => none

/-- StrWhiteSpace over `lo` to `hi` (`lo < hi`), built from the right. -/
def Cx.ws (cx : Cx) (lo hi : Nat) : Option Node := do
  let mut rest : Option Node := none
  for k in (List.range (hi - lo)).reverse do
    let i := lo + k
    let c ← cx.wsChar i
    rest := some (← cx.node .numericString .StrWhiteSpace 0 [rest.isSome] i hi
      #[(NT.StrWhiteSpaceChar.ctorIdx, some c), (NT.StrWhiteSpace.ctorIdx, rest)])
  rest

/-- A digit run over `lo` to `hi` (`lo < hi`): `ds :: d | ds d`, built from the left; `alt`
gives a code point's `one of` index in `d`. -/
def Cx.digits (cx : Cx) (ds d : NT) (alt : Nat → Option Nat) (lo hi : Nat) : Option Node := do
  if hi ≤ lo then none
  let digit (i : Nat) : Option Node := do
    let a ← alt (← cx.cs[i]?)
    cx.node .lexical d a [] i (i + 1) #[]
  let first ← cx.node .lexical ds 0 [] lo (lo + 1) #[(d.ctorIdx, some (← digit lo))]
  (List.range (hi - lo - 1)).foldlM (init := first) fun acc k => do
    let i := lo + 1 + k
    cx.node .lexical ds 1 [] lo (i + 1) #[(ds.ctorIdx, some acc), (d.ctorIdx, some (← digit i))]

def decAlt (c : Nat) : Option Nat := if 0x30 ≤ c && c ≤ 0x39 then some (c - 0x30) else none
def binAlt (c : Nat) : Option Nat := if c == 0x30 || c == 0x31 then some (c - 0x30) else none
def octAlt (c : Nat) : Option Nat := if 0x30 ≤ c && c ≤ 0x37 then some (c - 0x30) else none
/-- HexDigit's `one of`: `0`–`9`, `a`–`f`, `A`–`F`. -/
def hexAlt (c : Nat) : Option Nat :=
  if 0x30 ≤ c && c ≤ 0x39 then some (c - 0x30)
  else if 0x61 ≤ c && c ≤ 0x66 then some (c - 0x61 + 10)
  else if 0x41 ≤ c && c ≤ 0x46 then some (c - 0x41 + 16) else none

def Cx.decimalDigits (cx : Cx) (lo hi : Nat) : Option Node := cx.digits .DecimalDigits .DecimalDigit decAlt lo hi

/-- SignedInteger over `lo` to `hi`: DecimalDigits, `+` DecimalDigits, `-` DecimalDigits. -/
def Cx.signedInteger (cx : Cx) (lo hi : Nat) : Option Node := do
  let c ← cx.cs[lo]?
  let (alt, s) := if c == 0x2B then (1, lo + 1) else if c == 0x2D then (2, lo + 1) else (0, lo)
  let ds ← cx.decimalDigits s hi
  cx.node .lexical .SignedInteger alt [] lo hi #[(NT.DecimalDigits.ctorIdx, some ds)]

/-- ExponentPart over `lo` to `hi`: ExponentIndicator SignedInteger. -/
def Cx.exponentPart (cx : Cx) (lo hi : Nat) : Option Node := do
  let c ← cx.cs[lo]?
  let a ← if c == 0x65 then some 0 else if c == 0x45 then some 1 else none
  let e ← cx.node .lexical .ExponentIndicator a [] lo (lo + 1) #[]
  let s ← cx.signedInteger (lo + 1) hi
  cx.node .lexical .ExponentPart 0 [] lo hi #[(NT.ExponentIndicator.ctorIdx, some e), (NT.SignedInteger.ctorIdx, some s)]

/-- NonDecimalIntegerLiteral over `lo` to `hi`, if it starts with `0b`, `0o` or `0x` in either
case; `none` for no parse. -/
def Cx.nonDecimal (cx : Cx) (lo hi : Nat) : Option Node := do
  let p ← cx.cs[lo + 1]?
  let (alt, lit, ds, d, f) ←
    if p == 0x62 || p == 0x42 then some (0, NT.BinaryIntegerLiteral, NT.BinaryDigits, NT.BinaryDigit, binAlt)
    else if p == 0x6F || p == 0x4F then some (1, NT.OctalIntegerLiteral, NT.OctalDigits, NT.OctalDigit, octAlt)
    else if p == 0x78 || p == 0x58 then some (2, NT.HexIntegerLiteral, NT.HexDigits, NT.HexDigit, hexAlt)
    else none
  let n ← cx.digits ds d f (lo + 2) hi
  let l ← cx.node .lexical lit (if p < 0x60 then 1 else 0) [] lo hi #[(ds.ctorIdx, some n)]
  cx.node .lexical .NonDecimalIntegerLiteral alt [] lo hi #[(lit.ctorIdx, some l)]

/-- Whether `lo` to `hi` starts `0b`, `0o` or `0x` in either case. -/
def Cx.radixPrefix (cx : Cx) (lo hi : Nat) : Bool :=
  lo + 2 ≤ hi && cx.cs[lo]? == some 0x30 && (cx.cs[lo + 1]?.any fun p =>
    p == 0x62 || p == 0x42 || p == 0x6F || p == 0x4F || p == 0x78 || p == 0x58)

/-- The first index from `lo` to `hi` where `p` holds, else `hi`. -/
def Cx.find (cx : Cx) (lo hi : Nat) (p : Nat → Bool) : Nat :=
  ((List.range (hi - lo)).find? fun k => cx.cs[lo + k]?.any p).map (lo + ·) |>.getD hi

/-- StrUnsignedDecimalLiteral over `lo` to `hi`. -/
def Cx.unsignedDecimal (cx : Cx) (lo hi : Nat) : Option Node := do
  if (cx.cs.extract lo hi).toList == "Infinity".toList.map Char.toNat then
    return ← cx.node .numericString .StrUnsignedDecimalLiteral 0 [] lo hi #[]
  let ex := cx.find lo hi fun c => c == 0x65 || c == 0x45
  let exp ← if ex < hi then some <$> cx.exponentPart ex hi else some none
  let expKid := (NT.ExponentPart.ctorIdx, exp)
  let dot := cx.find lo ex (· == 0x2E)
  if dot < ex then
    let after ← if dot + 1 < ex then some <$> cx.decimalDigits (dot + 1) ex else some none
    if dot == lo then
      let a ← after
      cx.node .numericString .StrUnsignedDecimalLiteral 2 [exp.isSome] lo hi
        #[(NT.DecimalDigits.ctorIdx, some a), expKid]
    else
      let b ← cx.decimalDigits lo dot
      cx.node .numericString .StrUnsignedDecimalLiteral 1 [after.isSome, exp.isSome] lo hi
        #[(NT.DecimalDigits.ctorIdx, some b), (NT.DecimalDigits.ctorIdx, after), expKid]
  else
    let b ← cx.decimalDigits lo ex
    cx.node .numericString .StrUnsignedDecimalLiteral 3 [exp.isSome] lo hi #[(NT.DecimalDigits.ctorIdx, some b), expKid]

/-- StrNumericLiteral over `lo` to `hi`: StrDecimalLiteral, or NonDecimalIntegerLiteral. -/
def Cx.strNumeric (cx : Cx) (lo hi : Nat) : Option Node := do
  if cx.radixPrefix lo hi then
    let n ← cx.nonDecimal lo hi
    cx.node .numericString .StrNumericLiteral 1 [] lo hi #[(NT.NonDecimalIntegerLiteral.ctorIdx, some n)]
  else
    let c ← cx.cs[lo]?
    let (alt, s) := if c == 0x2B then (1, lo + 1) else if c == 0x2D then (2, lo + 1) else (0, lo)
    let u ← cx.unsignedDecimal s hi
    let d ← cx.node .numericString .StrDecimalLiteral alt [] lo hi #[(NT.StrUnsignedDecimalLiteral.ctorIdx, some u)]
    cx.node .numericString .StrNumericLiteral 0 [] lo hi #[(NT.StrDecimalLiteral.ctorIdx, some d)]

/-- StrIntegerLiteral over `lo` to `hi`: SignedInteger, or NonDecimalIntegerLiteral. -/
def Cx.strInteger (cx : Cx) (lo hi : Nat) : Option Node := do
  if cx.radixPrefix lo hi then
    let n ← cx.nonDecimal lo hi
    cx.node .numericString .StrIntegerLiteral 1 [] lo hi #[(NT.NonDecimalIntegerLiteral.ctorIdx, some n)]
  else
    let s ← cx.signedInteger lo hi
    cx.node .numericString .StrIntegerLiteral 0 [] lo hi #[(NT.SignedInteger.ctorIdx, some s)]

/-- A goal of the form `G ::: StrWhiteSpace? | StrWhiteSpace? M StrWhiteSpace?` over the whole
input, `body` parsing `M`. -/
def Cx.padded (cx : Cx) (goal body : NT) (inner : Cx → Nat → Nat → Option Node) : Option Node := do
  let n := cx.cs.size
  let a := cx.find 0 n fun c => !isStrWhiteSpaceChar c
  let lead ← if 0 < a then some <$> cx.ws 0 a else some none
  if a == n then
    cx.node .numericString goal 0 [lead.isSome] 0 n #[(NT.StrWhiteSpace.ctorIdx, lead)]
  else
    let b := n - ((List.range (n - a)).find? (fun k => !(cx.cs[n - 1 - k]?.any isStrWhiteSpaceChar))).getD 0
    let trail ← if b < n then some <$> cx.ws b n else some none
    let m ← inner cx a b
    cx.node .numericString goal 1 [lead.isSome, trail.isSome] 0 n
      #[(NT.StrWhiteSpace.ctorIdx, lead), (body.ctorIdx, some m), (NT.StrWhiteSpace.ctorIdx, trail)]

/-- `n` with the root's parameters `ps`. -/
def withArgs (ps : List Ecma.Grammar.Param) : Node → Node
  | .mk st lo hi p nt _ kids t => .mk st lo hi p nt ps kids t

/-- `Model.parse` at Impl: `some (some n)` the Parse Node, its root with the parameters `args` switch
on, `some none` no parse, for the goals StringNumericLiteral and StringIntegerLiteral; `none`
(undecided) otherwise. -/
def parseNumeric (stamp : Nat) (src : Array MathVal) (goal : NtId) (args : List (ParamId × Bool)) :
    Option (Option Node) := do
  let cs ← src.mapM fun | .int i => if 0 ≤ i ∧ i ≤ 0x10FFFF then some i.toNat else none | _ => none
  let cx : Cx := ⟨cs, stamp⟩
  let root := Option.map (withArgs (Engine.Parse.paramsOfArgs args))
  if goal == NT.StringNumericLiteral.ctorIdx then some (root (cx.padded .StringNumericLiteral .StrNumericLiteral Cx.strNumeric))
  else if goal == NT.StringIntegerLiteral.ctorIdx then some (root (cx.padded .StringIntegerLiteral .StrIntegerLiteral Cx.strInteger))
  else none

end Engine
