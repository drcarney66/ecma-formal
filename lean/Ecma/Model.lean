module

public import Ecma.Notation.Syntax
public import Ecma.Grammar.Core

@[expose] public section

/-!
# Ecma models: the spec's sorts, abstract

A `Model` gives each sort of the specification a carrier and its operations.
The machine is defined over every model; the laws a model must satisfy are a
separate statement (`Model.Laws`). No carrier is fixed here: mathematical
values form an ordered field with "is an integer" a predicate; Strings are
sequences of code units; Lists, Records and objects live in a store and have
identity.
-/

namespace Ecma

/-- The case view of a Number value (§6.1.6.1). -/
inductive NumView (Math : Type) where
  | nan
  | posInf
  | negInf
  | posZero
  | negZero
  /-- a finite non-zero value: its mathematical value -/
  | finite (m : Math)

/-- A parser invocation's context (§5.1.2): the Annex B sections whose grammar applies (those the host
supports, B.1 and B.3), whether the source text is strict mode code from outside (§11.2.2: eval code of a
direct eval in strict mode code), whether it is parsed for ParseJSON (§25.5.1), and whether it is
source text parsed with the goal symbol |Module| (B.1.1), or a reparse of tokens such a parse matched. -/
structure ParseCx where
  annexB : Grammar.AnnexB.Set
  strict : Bool
  json : Bool
  module : Bool
  deriving Repr, BEq, Inhabited

/-- The Unicode Normalization Forms (UAX #15). -/
inductive NormForm where
  | NFC | NFD | NFKC | NFKD
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A model of the spec's sorts and their primitive operations. -/
structure Model where
  /-- mathematical values (§5.2.6) -/
  Math : Type
  /-- Number values (§6.1.6.1) -/
  Num : Type
  /-- BigInt values (§6.1.6.2) -/
  Big : Type
  /-- String values: sequences of 16-bit code units (§6.1.4) -/
  Str : Type
  /-- Symbol values: identities (§6.1.5) -/
  Sym : Type
  /-- identities of store cells: objects, Records and Lists -/
  Addr : Type
  /-- Parse Nodes (§5.1.2) -/
  Node : Type
  /-- finite sequences: List contents (§6.2.2) -/
  Seq : Type → Type
  /-- byte sequences: Data Block contents (§6.2.9) -/
  Bytes : Type
  /-- finite maps from field names: Record contents and internal slots (§6.2.1) -/
  Rec : Type → Type
  /-- own-property tables: maps from property keys, in creation order (§6.1.7) -/
  Props : Type → Type
  /-- the store -/
  Heap : Type → Type

  /-- a numeral -/
  ofNat : Nat → Math
  add : Math → Math → Math
  sub : Math → Math → Math
  mul : Math → Math → Math
  div : Math → Math → Math
  neg : Math → Math
  /-- `x<sup>y</sup>`: for an integer y, or for x > 0 and any y -/
  pow : Math → Math → Math
  lt : Math → Math → Bool
  eq : Math → Math → Bool
  /-- the largest integer ≤ x -/
  floor : Math → Math
  /-- "x is an integer" -/
  isInt : Math → Bool
  /-- the integer e with 10^e ≤ x < 10^(e+1), for x > 0: the place of the first significant digit of x's decimal
  representation (`Model.Laws`) -/
  decExp : Math → Math
  /-- the square root of a non-negative mathematical value -/
  sqrt : Math → Math
  /-- π -/
  pi : Math
  /-- a §21.3 function at x, on the domain the calling steps guard; opaque: every use is
  implementation-approximated -/
  fn : MathFn → Math → Math

  numView : Num → NumView Math
  /-- 𝔽(x) for finite x: roundTiesToEven to the nearest Number value (§6.1.6.1) -/
  numOf : Math → Num
  numNaN : Num
  /-- +∞𝔽 (false) or -∞𝔽 (true) -/
  numInf : Bool → Num
  /-- +0𝔽 (false) or -0𝔽 (true) -/
  numZero : Bool → Num
  /-- IEEE 754-2019 addition, roundTiesToEven (§5.2.6: operators on Numbers) -/
  numAdd : Num → Num → Num
  numSub : Num → Num → Num
  numMul : Num → Num → Num
  numDiv : Num → Num → Num
  numNeg : Num → Num
  /-- IEEE 754-2019 compareQuietLess -/
  numLt : Num → Num → Bool
  /-- IEEE 754-2019 compareQuietEqual -/
  numEq : Num → Num → Bool
  /-- Number::toString's integers n, k and s for a finite positive Number and a radix from 2 to 36 (§6.1.6.1.20
  step 5): s has k digits, 𝔽(s × radix^(n-k)) is the Number, and k is as small as possible (`Model.NumLaws`) -/
  numDigits : Num → Math → Math × Nat × Math

  /-- ℤ(x) for an integer x -/
  bigOf : Math → Big
  /-- ℝ(x) -/
  bigVal : Big → Math

  /-- a String literal of the text -/
  strLit : String → Str
  strLen : Str → Math
  /-- the code unit at an index, as a mathematical value -/
  strAt : Str → Math → Option Math
  strConcat : Str → Str → Str
  /-- the substring from `i` to `j` -/
  strSub : Str → Math → Math → Str
  /-- the String of one code unit -/
  strOfUnit : Math → Str
  /-- the String made from `n` copies of `s` appended together (`n ≥ 0`) -/
  strRepeat : Math → Str → Str
  /-- the representation of non-negative integer `n` using radix `r` (`2 ≤ r ≤ 36`) -/
  intToRadix : Math → Math → Str
  strEq : Str → Str → Bool
  /-- the code units, first to last -/
  strUnits : Str → Seq Math

  symEq : Sym → Sym → Bool
  /-- a Symbol's [[Description]]: a String, or none for *undefined* (§6.1.5) -/
  symDesc : Sym → Option Str
  /-- the Symbol made by the `k`th creation, with the description -/
  symNew : Nat → Option Str → Sym
  addrEq : Addr → Addr → Bool

  nodeProd : Node → ProdId
  /-- the `k`-th written occurrence of a nonterminal on the production's right-hand side, absent
  optional items counted: `some (some c)` its child, `some none` an optional item that is absent,
  `none` no such occurrence -/
  nodeChild : Node → NtId → Nat → Option (Option Node)
  /-- the children, left to right (§5.1.2) -/
  nodeKids : Node → Seq Node
  /-- the proper descendants, in pre-order -/
  nodeDescendants : Node → Seq Node
  /-- the nonterminal the node is an instance of -/
  nodeNt : Node → NtId
  /-- the code points of the source text it matched (§11) -/
  nodeSource : Node → Seq Math
  /-- the grammatical parameters it was parsed with (§5.1.6) -/
  nodeArgs : Node → List Grammar.Param
  /-- §5.1.2 parser invocation `k`, the errata read as `rd`: a parse of code points with a goal
  symbol and its parameters, `some (some n)` the Parse Node, `some none` no parse, `none` where the
  model does not decide (`Model.ParseLaws`) -/
  parse : (ErratumId → Reading) → ParseCx → Nat → Seq Math → NtId → List (ParamId × Bool) → Option (Option Node)
  /-- §5.1.5 "P must cover K": the covered Parse Node of parser invocation `k`, the errata read as `rd`:
  the Parse Node the cover's source text parses to with the goal symbol and its parameters, given from
  the cover itself; `none` where the model gives none from the cover, and its source text is parsed
  (`Model.CoverLaws`) -/
  cover : (ErratumId → Reading) → ParseCx → Nat → Node → NtId → List (ParamId × Bool) → Option Node :=
    fun _ _ _ _ _ _ => none
  /-- the parser invocation a Parse Node resulted from (§5.1.2: never reused across invocations) -/
  nodeStamp : Node → Nat
  /-- the span of source text it matched, in code points -/
  nodeSpan : Node → Nat × Nat
  /-- `nodeParent r n`: the Parse Node of which `n` is a child, in the tree below `r`; none where
  there is none (`Model.ParentLaws`) -/
  nodeParent : Node → Node → Option Node
  /-- `nodeAncestors r n`: the Parse Nodes of the tree below `r` that contain `n`, the nearest first: its
  parent, that node's parent, and so on to `r` (`Model.ParentLaws`) -/
  nodeAncestors : Node → Node → List Node
  /-- a bound on the depth of the tree below it: more than each child's (`Model.ParentLaws`) -/
  nodeHeight : Node → Nat
  /-- whether two Parse Nodes are the same one -/
  nodeEq : Node → Node → Bool

  seqNil : {α : Type} → Seq α
  seqPush : {α : Type} → Seq α → α → Seq α
  seqCons : {α : Type} → α → Seq α → Seq α
  seqLen : {α : Type} → Seq α → Math
  seqGet : {α : Type} → Seq α → Math → Option α
  seqSet : {α : Type} → Seq α → Math → α → Seq α
  seqConcat : {α : Type} → Seq α → Seq α → Seq α
  seqRemove : {α : Type} → Seq α → Math → Seq α
  /-- `n` copies of a value, for a non-negative integer `n` -/
  seqRepeat : {α : Type} → Math → α → Seq α
  /-- the elements, first to last, folded -/
  seqFoldl : {α β : Type} → (β → α → β) → β → Seq α → β

  recEmpty : {α : Type} → Rec α
  recGet : {α : Type} → Rec α → FieldId → Option α
  recSet : {α : Type} → Rec α → FieldId → α → Rec α
  recDel : {α : Type} → Rec α → FieldId → Rec α
  recKeys : {α : Type} → Rec α → Seq FieldId

  propsEmpty : {α : Type} → Props α
  propsGet : {α : Type} → Props α → Str ⊕ Sym → Option α
  /-- update in place, or add at the end of creation order -/
  propsPut : {α : Type} → Props α → Str ⊕ Sym → α → Props α
  propsDel : {α : Type} → Props α → Str ⊕ Sym → Props α
  /-- the keys in creation order -/
  propsKeys : {α : Type} → Props α → Seq (Str ⊕ Sym)

  heapEmpty : {α : Type} → Heap α
  /-- a fresh address -/
  heapAlloc : {α : Type} → Heap α → α → Addr × Heap α
  heapGet : {α : Type} → Heap α → Addr → Option α
  heapSet : {α : Type} → Heap α → Addr → α → Heap α

  /-- the simple case folding of a code point: its CaseFolding.txt mapping of status C or S, if
  any (UAX #44 Simple_Case_Folding) -/
  scf? : Math → Option Math
  /-- toLowercase (Unicode §3.13, Default Case Conversion): full lowercase mappings, Final_Sigma
  in context -/
  toLower : Seq Math → Seq Math
  /-- toUppercase (Unicode §3.13, Default Case Conversion): full uppercase mappings -/
  toUpper : Seq Math → Seq Math
  /-- the CharSetElements, each a sequence of code points, whose Unicode Character Database
  definition includes the property named p with the value named v (names or aliases, as code
  points; §22.2.2.9); `none` where p and v name no property value, or one with infinitely
  many elements (False of a property of strings) -/
  propSet : Seq Math → Seq Math → Option (Seq (Seq Math))
  /-- the long name, as code points, of the value named v of the Unicode property named p (names
  or aliases, compared exactly; PropertyValueAliases.txt); `none` where p and v name none -/
  propValue : Seq Math → Seq Math → Option (Seq Math)
  /-- the code points normalized into the form, as the Unicode Standard's Normalization Forms
  specify (UAX #15); opaque -/
  normalize : NormForm → Seq Math → Seq Math

  CharSet : Type
  csEmpty : CharSet
  csAdd : CharSet → Seq Math → CharSet
  csInterval : Math → Math → CharSet
  csUnion : CharSet → CharSet → CharSet
  csInter : CharSet → CharSet → CharSet
  csDiff : CharSet → CharSet → CharSet
  csHas : CharSet → Seq Math → Bool
  csSize : CharSet → Math
  csGet : CharSet → Math → Option (Seq Math)
  csAllSingle : CharSet → Bool
  csSingles : CharSet → CharSet
  csFromProp : Seq Math → Seq Math → Option CharSet
  csNoScf : CharSet
  csCanonExtra : CharSet → Bool → CharSet
  csHasCanon : CharSet → Math → Bool → Bool → Bool

  /-- a Data Block of `n` zero bytes (§6.2.9, empty if not a non-negative integer) -/
  bytesZero : Math → Bytes
  bytesLen : Bytes → Math
  bytesGet : Bytes → Math → Option Math
  bytesSet : Bytes → Math → Math → Bytes
  bytesFill : Bytes → Math → Bytes

/-- A List's elements, first to last. -/
def seqList {M : Model} {α : Type} (sq : M.Seq α) : List α := M.seqFoldl (fun l x => l ++ [x]) [] sq

/-- §22.2.2.7.3 Canonicalize(rer, ch) on a character `c`, with [[IgnoreCase]] `ignoreCase` and
HasEitherUnicodeFlag `u`. -/
def Model.canonChar (M : Model) (ignoreCase u : Bool) (c : M.Math) : M.Math :=
  if !ignoreCase then c
  else if u then (M.scf? c).getD c
  else
    let mapped := M.toUpper (M.seqPush M.seqNil c)
    if M.eq (M.seqLen mapped) (M.ofNat 1) then
      match M.seqGet mapped (M.ofNat 0) with
      | some d => if M.lt (M.ofNat 0xFFFF) d || (!M.lt c (M.ofNat 128) && M.lt d (M.ofNat 128)) then c else d
      | none => c
    else c

end Ecma
