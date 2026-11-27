module

public import Ecma.State

@[expose] public section

/-!
# Notation primitives: Strings and code points

The prose notation of §6.1.4 and §11 over Strings, code units and code points.
A code unit or a code point is a mathematical value: an integer 0–0xFFFF or
0–0x10FFFF. A String is `M.Str`; where the text allows "a sequence of code
units", a List of code units stands for the String. Source text is a List of
code points (§11).
-/

namespace Ecma.Prims.Strings

section
variable {M : Model}

/-- An integer in `[0, hi]`. -/
def inRange (hi : Nat) (m : M.Math) : Bool :=
  M.isInt m && !M.lt m (M.ofNat 0) && !M.lt (M.ofNat hi) m

/-- A code unit's value (§6.1.4, sec-ecmascript-language-types-string-type). -/
def isUnit (m : M.Math) : Bool := inRange 0xFFFF m

/-- A code point's value (§6.1.4, sec-ecmascript-language-types-string-type). -/
def isPoint (m : M.Math) : Bool := inRange 0x10FFFF m

/-- The String of a List's elements: a code unit, or the code units of a String. -/
def unitsOfSeq (xs : M.Seq (Val M)) : Option M.Str :=
  M.seqFoldl (fun acc v => match acc, v with
    | some t, .math u => if isUnit u then some (M.strConcat t (M.strOfUnit u)) else none
    | some t, .str u => some (M.strConcat t u)
    | _, _ => none) (some (M.strLit "")) xs

/-- A String value, or a sequence of code units as a List, as a String (§6.1.4). -/
def units (v : Val M) : Run M M.Str :=
  match v with
  | .str s => Run.pure s
  | .ref a => do
    match ← readCell a with
    | .list xs _ => optOr .sortError (unitsOfSeq xs)
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- A String, a sequence of code units, or one code unit, as a String. -/
def unitsOrUnit (v : Val M) : Run M M.Str :=
  match v with
  | .math u => if isUnit u then Run.pure (M.strOfUnit u) else Run.stop .sortError
  | v => units v

/-- The elements of a List value. -/
def seqOf (v : Val M) : Run M (M.Seq (Val M)) :=
  match v with
  | .ref a => do
    match ← readCell a with
    | .list xs _ => Run.pure xs
    | _ => Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.4 "the code unit 0xNNNN": the code unit whose value is e. -/
def codeUnit (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.math m] => if isUnit m then Run.pure (.math m) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.4 "the String value consisting of a, b": the code units of each, in order. -/
def strOfUnits (vs : List (Val M)) : Run M (Val M) :=
  match vs.foldl (fun acc v => match acc, v with
    | some t, .math u => if isUnit u then some (M.strConcat t (M.strOfUnit u)) else none
    | some t, .str u => some (M.strConcat t u)
    | _, _ => none) (some (M.strLit "")) with
  | some t => Run.pure (.str t)
  | none => Run.stop .sortError

/-- §6.1.4 StringRepeat(s, n): the String made from n copies of s appended together, for a non-negative
integer n: the string-concatenation of the n copies of the model's sequence of n copies (`seqRepeat`). -/
def stringRepeat (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.str s, .math n] =>
    if !(M.isInt n && !M.lt n (M.ofNat 0)) then Run.stop .sortError
    else Run.pure (.str (M.strRepeat n s))
  | _ => Run.stop .sortError

/-- The substring of `t` from `i` to `j`, for integers `0 ≤ i ≤ j ≤` the length of `t`. -/
def subOf (t : M.Str) (i j : M.Math) : Run M (Val M) :=
  if !(M.isInt i && M.isInt j) then Run.stop .sortError
  else if M.lt i (M.ofNat 0) || M.lt j i || M.lt (M.strLen t) j then Run.stop .residue
  else Run.pure (.str (M.strSub t i j))

/-- §6.1.4 "the substring of s from i to j": the code units of s from index i up to j, or to
the end when j is absent. -/
def substring (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [s, .math i] => do let t ← units s; subOf t i (M.strLen t)
  | [s, .math i, .absent] => do let t ← units s; subOf t i (M.strLen t)
  | [s, .math i, .choice 1] => do let t ← units s; subOf t i (M.strLen t)
  | [s, .math i, .choice 1, .absent] => do let t ← units s; subOf t i (M.strLen t)
  | [s, .math i, .math j] => do subOf (← units s) i j
  | [s, .math i, .choice 0, .math j] => do subOf (← units s) i j
  | _ => Run.stop .sortError

/-- §6.1.4 "the length of s": the number of code units of s. -/
def strLen (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [s] => do return .math (M.strLen (← units s))
  | _ => Run.stop .sortError

/-- §6.1.4 "the code unit at index i within s". -/
def unitAt (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.math i, s] => do
    match M.strAt (← units s) i with
    | some u => Run.pure (.math u)
    | none => if M.isInt i then Run.stop .residue else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.4 "the numeric value of c": a code unit's or a code point's value. -/
def numericValue (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.math m] => if isPoint m then Run.pure (.math m) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §6.1.4 "the first code unit of s": the code unit at index 0 of a non-empty s. -/
def firstUnit (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [s] => do
    match M.strAt (← units s) (M.ofNat 0) with
    | some u => Run.pure (.math u)
    | none => Run.stop .residue
  | _ => Run.stop .sortError

/-- §6.1.4 "s starts with x": x's code units are the first code units of s. -/
def startsWith (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [x, subject] => do
    let p ← unitsOrUnit x
    let s ← units subject
    let n := M.strLen p
    return .bool (!M.lt (M.strLen s) n && M.strEq (M.strSub s (M.ofNat 0) n) p)
  | _ => Run.stop .sortError

/-- The number of code points of a source text that are not `c`. -/
def countExcept (xs : M.Seq (Val M)) (c : Option M.Math) : Option M.Math :=
  M.seqFoldl (fun acc v => match acc, v with
    | some k, .math x =>
      if !isPoint x then none
      else match c with
        | some y => if M.eq x y then some k else some (M.add k (M.ofNat 1))
        | none => some (M.add k (M.ofNat 1))
    | _, _ => none) (some (M.ofNat 0)) xs

/-- The number of code points of `n`'s source outside every occurrence of nonterminal `k` within
it (§5.2.2): its source's length less that of each instance of `k` among its descendants not
within another. -/
def pointsExcept (n : M.Node) (k : NtId) : M.Math :=
  let xs := (M.seqFoldl (fun acc d => if M.nodeNt d == k then d :: acc else acc) [] (M.nodeDescendants n)).reverse
  let within (d e : M.Node) : Bool :=
    (M.nodeSpan e).1 ≤ (M.nodeSpan d).1 && (M.nodeSpan d).2 ≤ (M.nodeSpan e).2 && !(M.nodeSpan d == M.nodeSpan e)
  let outer := xs.filter fun d => !xs.any (within d ·)
  outer.foldl (fun m d => M.sub m (M.seqLen (M.nodeSource d))) (M.seqLen (M.nodeSource n))

/-- §11 "the number of code points in s, excluding all occurrences of x": over a source text or
a Parse Node's (a nonterminal's instances excluded); a String stops with residue. -/
def codePointCount (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.ref a, .absent] => do return .math (← optOr .sortError (countExcept (← seqOf (.ref a)) none))
  | [.ref a, .math c] =>
    if isPoint c then do return .math (← optOr .sortError (countExcept (← seqOf (.ref a)) (some c)))
    else Run.stop .sortError
  | [.ref _, .nt _ _] => Run.stop .residue
  | [.ref _, .node _] => Run.stop .residue
  | [.node n, .absent] => Run.pure (.math (M.seqLen (M.nodeSource n)))
  | [.node n, .nt k _] => Run.pure (.math (pointsExcept n k))
  | [.node _, _] => Run.stop .residue
  | [.str _, _] => Run.stop .residue
  | _ => Run.stop .sortError

/-- §6.1.4 "the code point (0) or code unit (1) whose numeric value is n". -/
def unitOrPointOf (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.choice 0, .math n] => if isPoint n then Run.pure (.math n) else Run.stop .sortError
  | [.choice 1, .math n] => if isUnit n then Run.pure (.math n) else Run.stop .sortError
  | _ => Run.stop .sortError

/-- Whether a code unit is a leading surrogate (§6.1.4, sec-ecmascript-language-types-string-type). -/
def isLead (u : M.Math) : Bool := !M.lt u (M.ofNat 0xD800) && !M.lt (M.ofNat 0xDBFF) u

/-- Whether a code unit is a trailing surrogate (§6.1.4, sec-ecmascript-language-types-string-type). -/
def isTrail (u : M.Math) : Bool := !M.lt u (M.ofNat 0xDC00) && !M.lt (M.ofNat 0xDFFF) u

/-- §11.1.4 (sec-utf16decodesurrogatepair): the code point of a surrogate pair. -/
def pairValue (c1 c2 : M.Math) : M.Math :=
  M.add (M.add (M.mul (M.sub c1 (M.ofNat 0xD800)) (M.ofNat 0x400)) (M.sub c2 (M.ofNat 0xDC00)))
    (M.ofNat 0x10000)

/-- §6.1.4 (sec-ecmascript-language-types-string-type): a String's code points: a lead and trail surrogate pair as
one, any other code unit as itself. -/
def strPoints (t : M.Str) : M.Seq M.Math :=
  let (acc, pend) := M.seqFoldl (fun (st : M.Seq M.Math × Option M.Math) u => match st with
    | (acc, some l) =>
      if isTrail u then (M.seqPush acc (pairValue l u), none)
      else if isLead u then (M.seqPush acc l, some u)
      else (M.seqPush (M.seqPush acc l) u, none)
    | (acc, none) => if isLead u then (acc, some u) else (M.seqPush acc u, none))
    (M.seqNil, none) (M.strUnits t)
  match pend with
  | some l => M.seqPush acc l
  | none => acc

/-- §11 "the code point matched by node": the single code point of node's source text; a stop
unless it has exactly one. -/
def codePointMatched (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.node n] =>
    let s := M.nodeSource n
    if M.eq (M.seqLen s) (M.ofNat 1) then
      match M.seqGet s (M.ofNat 0) with
      | some c => Run.pure (.math c)
      | none => Run.stop .sortError
    else Run.stop .sortError
  | _ => Run.stop .sortError

/-- §11 "the List of Unicode code points p": source text p, a List of code points, itself; a
String's code points (§6.1.4) as a new List. -/
def codePoints (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.ref a] => do
    let xs ← seqOf (.ref a)
    if M.seqFoldl (fun ok v => ok && match v with | .math x => isPoint x | _ => false) true xs
    then Run.pure (.ref a) else Run.stop .sortError
  | [.str t] => do
    return .ref (← alloc (.list (M.seqFoldl (fun acc x => M.seqPush acc (.math x)) M.seqNil (strPoints t)) 0))
  | _ => Run.stop .sortError

/-- §11 "the empty sequence of Unicode code points": a new empty List. -/
def emptyCodePoints (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [] => listOf []
  | _ => Run.stop .sortError

/-- §11 "the source text matched by node": a new List of node's code points. -/
def sourceText (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.node n] => do
    return .ref (← alloc (.list (M.seqFoldl (fun acc x => M.seqPush acc (.math x)) M.seqNil (M.nodeSource n)) 0))
  | _ => Run.stop .sortError

/-- A case mapping of a List of code points (Unicode §3.13): a new List of the mapped code points. -/
def caseMap (f : M.Seq M.Math → M.Seq M.Math) (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [v@(.ref _)] => do
    let xs ← seqOf v
    match M.seqFoldl (fun acc v => match acc, v with
        | some s, .math x => if isPoint x then some (M.seqPush s x) else none
        | _, _ => none) (some M.seqNil) xs with
    | some cs => return .ref (← alloc (.list (M.seqFoldl (fun acc x => M.seqPush acc (.math x)) M.seqNil (f cs)) 0))
    | none => Run.stop .sortError
  | _ => Run.stop .sortError

/-- The normalization form a String names: "NFC", "NFD", "NFKC" or "NFKD". -/
def normFormOf (s : M.Str) : Option NormForm :=
  ([("NFC", NormForm.NFC), ("NFD", .NFD), ("NFKC", .NFKC), ("NFKD", .NFKD)].find?
    fun p => M.strEq s (M.strLit p.1)).map (·.2)

/-- §6.1.4 CodePointsToString: the UTF-16 code units of code points, as a String; none if one is
not a code point. -/
def pointsStr (cs : M.Seq M.Math) : Option M.Str :=
  M.seqFoldl (fun acc c => acc.bind fun t =>
    if !isPoint c then none
    else if M.lt c (M.ofNat 0x10000) then some (M.strConcat t (M.strOfUnit c))
    else
      let d := M.sub c (M.ofNat 0x10000)
      let hi := M.floor (M.div d (M.ofNat 0x400))
      some (M.strConcat (M.strConcat t (M.strOfUnit (M.add hi (M.ofNat 0xD800))))
        (M.strOfUnit (M.add (M.sub d (M.mul hi (M.ofNat 0x400))) (M.ofNat 0xDC00)))))
    (some (M.strLit "")) cs

/-- A key as a table's cells hold it: a List of code points is the String of them (a code entry
is the code points it is written as); any other value is itself. -/
def codeKey (key : Val M) : Run M (Val M) := do
  match key with
  | .ref a => match ← readCell a with
    | .list xs _ =>
      let cps := M.seqFoldl (fun acc v => match acc, v with
        | some s, .math x => some (M.seqPush s x)
        | _, _ => none) (some M.seqNil) xs
      match cps.bind pointsStr with
      | some t => return .str t
      | none => return key
    | _ => return key
  | _ => return key

/-- UnicodeNormalize(s, form): the code points of s normalized into the normalization form that
form names (UAX #15, `Model.normalize`), as a String. -/
def unicodeNormalize (vs : List (Val M)) : Run M (Val M) :=
  match vs with
  | [.str t, .str form] => do
    let f ← optOr .sortError (normFormOf form)
    return .str (← optOr .sortError (pointsStr (M.normalize f (strPoints t))))
  | _ => Run.stop .sortError

/-- The Strings family's primitives, by id; `none` for another family's. -/
def prim (p : PrimId) (vs : List (Val M)) : Option (Run M (Val M)) :=
  if p == Known.pCodeUnit then some (codeUnit vs)
  else if p == Known.pStrOfUnits then some (strOfUnits vs)
  else if p == Known.pStringRepeat then some (stringRepeat vs)
  else if p == Known.pSubstring then some (substring vs)
  else if p == Known.pStrLen then some (strLen vs)
  else if p == Known.pUnitAt then some (unitAt vs)
  else if p == Known.pNumericValue then some (numericValue vs)
  else if p == Known.pFirstUnit then some (firstUnit vs)
  else if p == Known.pStartsWith then some (startsWith vs)
  else if p == Known.pCodePointCount then some (codePointCount vs)
  else if p == Known.pUnitOrPointOf then some (unitOrPointOf vs)
  else if p == Known.pCodePointMatched then some (codePointMatched vs)
  else if p == Known.pCodePoints then some (codePoints vs)
  else if p == Known.pEmptyCodePoints then some (emptyCodePoints vs)
  else if p == Known.pSourceText then some (sourceText vs)
  else if p == Known.pToLowercase then some (caseMap M.toLower vs)
  else if p == Known.pToUppercase then some (caseMap M.toUpper vs)
  else if p == Known.pUnicodeNormalize then some (unicodeNormalize vs)
  else none

end

end Ecma.Prims.Strings
