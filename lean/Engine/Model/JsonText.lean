module

@[expose] public section

/-!
# ECMA-404's grammar: the JSON text recognizer

ECMA-404's grammar (spec/formal/json.emu), one recognizer per production: each consumes the
longest prefix its production derives, which is the only one that can be followed by valid input.
Generic over the code point type, through its tests.
-/

namespace Engine.JsonText

/-- Tests on a code point: whether it is the code point `n`, whether it is below `n`. -/
structure CpTests (α : Type) where
  is : α → Nat → Bool
  below : α → Nat → Bool

variable {α : Type} (T : CpTests α)

/-- A recognizer's outcome on `xs`: the input after the prefix it matched, shorter than `xs`. -/
abbrev Rest (xs : List α) := Option {r : List α // r.length < xs.length}

/-- An optional part's outcome on `xs`: the input after the prefix it matched, if any. -/
abbrev Opt (xs : List α) := {r : List α // r.length ≤ xs.length}

/-- An outcome on a suffix `ys` of `xs`, as one on `xs`. -/
def lift {xs ys : List α} (h : ys.length ≤ xs.length) : Rest ys → Rest xs
  | some ⟨r, hr⟩ => some ⟨r, by omega⟩
  | none => none

/-- `p`, then `q` on the rest. -/
def seq {xs : List α} (p : Rest xs) (q : (ys : List α) → Rest ys) : Rest xs :=
  match p with
  | some ⟨r, h⟩ => lift (Nat.le_of_lt h) (q r)
  | none => none

/-- `p`, then the optional `q` on the rest. -/
def seqOpt {xs : List α} (p : Rest xs) (q : (ys : List α) → Opt ys) : Rest xs :=
  match p with
  | some ⟨r, h⟩ => let o := q r; some ⟨o.1, by have := o.2; omega⟩
  | none => none

/-- `p?`: `p` if it matches, else nothing. -/
def opt (p : (ys : List α) → Rest ys) (xs : List α) : Opt xs :=
  match p xs with
  | some ⟨r, h⟩ => ⟨r, Nat.le_of_lt h⟩
  | none => ⟨xs, Nat.le_refl _⟩

/-- The optional `p`, then `q` on the rest. -/
def optSeq {xs : List α} (p : Opt xs) (q : (ys : List α) → Rest ys) : Rest xs :=
  lift p.2 (q p.1)

/-- Whether `c` is in the inclusive interval from `lo` to `hi`. -/
def inRange (c : α) (lo hi : Nat) : Bool := !T.below c lo && T.below c (hi + 1)

/-- The code point `n`. -/
def cp (n : Nat) : (xs : List α) → Rest xs
  | c :: cs => if T.is c n then some ⟨cs, by simp⟩ else none
  | [] => none

/-- The code points `ns`, in order. -/
def cps : List Nat → (xs : List α) → Rest xs
  | [], _ => none
  | n :: ns, c :: cs =>
    if !T.is c n then none
    else if ns.isEmpty then some ⟨cs, by simp⟩
    else lift (by simp <;> omega) (cps ns cs)
  | _ :: _, [] => none

/-- A code point of the class `p`. -/
def cpOf (p : α → Bool) : (xs : List α) → Rest xs
  | c :: cs => if p c then some ⟨cs, by simp⟩ else none
  | [] => none

/-- JSONWhiteSpaceCharacter (ECMA-404 §4). -/
def isWhiteSpaceCharacter (c : α) : Bool := T.is c 0x09 || T.is c 0x0A || T.is c 0x0D || T.is c 0x20

/-- JSONWhiteSpace? (§4): the input after its longest prefix of white space. -/
def whiteSpace : (xs : List α) → Opt xs
  | c :: cs =>
    if isWhiteSpaceCharacter T c then let r := whiteSpace cs; ⟨r.1, by have := r.2; simp; omega⟩
    else ⟨c :: cs, Nat.le_refl _⟩
  | [] => ⟨[], Nat.le_refl _⟩

/-- JSONDigit (§8). -/
def isDigit (c : α) : Bool := inRange T c 0x30 0x39

/-- JSONNonZeroDigit (§8). -/
def isNonZeroDigit (c : α) : Bool := inRange T c 0x31 0x39

/-- JSONExponentIndicator (§8): `e` or `E`. -/
def isExponentIndicator (c : α) : Bool := T.is c 0x65 || T.is c 0x45

/-- JSONSign (§8): `+` or `-`. -/
def isSign (c : α) : Bool := T.is c 0x2B || T.is c 0x2D

/-- JSONDigits (§8): the longest non-empty run of digits. -/
def digits : (xs : List α) → Rest xs
  | c :: cs =>
    if !isDigit T c then none
    else match digits cs with
      | some ⟨r, h⟩ => some ⟨r, by simp <;> omega⟩
      | none => some ⟨cs, by simp⟩
  | [] => none

/-- JSONInteger (§8): `0`, or a non-zero digit and its digits. -/
def integer (xs : List α) : Rest xs :=
  (cp T 0x30 xs).or (seqOpt (cpOf (isNonZeroDigit T) xs) (opt (digits T)))

/-- JSONFraction (§8): `.` and digits. -/
def fraction (xs : List α) : Rest xs := seq (cp T 0x2E xs) (digits T)

/-- JSONExponent (§8): an exponent indicator, an optional sign, digits. -/
def exponent (xs : List α) : Rest xs :=
  seq (cpOf (isExponentIndicator T) xs) fun ys => optSeq (opt (cpOf (isSign T)) ys) (digits T)

/-- JSONNumber (§8): an optional `-`, an integer, an optional fraction and exponent. -/
def number (xs : List α) : Rest xs :=
  seqOpt (seqOpt (optSeq (opt (cp T 0x2D) xs) (integer T)) (opt (fraction T))) (opt (exponent T))

/-- JSONHexDigit (§9). -/
def isHexDigit (c : α) : Bool := isDigit T c || inRange T c 0x41 0x46 || inRange T c 0x61 0x66

/-- JSONSingleEscapeCharacter (§9): `"` `\` `/` `b` `f` `n` `r` `t`. -/
def isSingleEscapeCharacter (c : α) : Bool := [0x22, 0x5C, 0x2F, 0x62, 0x66, 0x6E, 0x72, 0x74].any (T.is c)

/-- JSONControlCharacter (§9): U+0000 to U+001F. -/
def isControlCharacter (c : α) : Bool := T.below c 0x20

/-- JSONEscape (§9): a single escape character, or `u` and four hex digits. -/
def escape (xs : List α) : Rest xs :=
  (cpOf (isSingleEscapeCharacter T) xs).or <|
    seq (cp T 0x75 xs) fun ys => seq (cpOf (isHexDigit T) ys) fun ys => seq (cpOf (isHexDigit T) ys)
      fun ys => seq (cpOf (isHexDigit T) ys) (cpOf (isHexDigit T))

/-- JSONStringCharacter (§9): a code point but not `"`, `\` or a control character; or `\` and an
escape. -/
def stringCharacter (xs : List α) : Rest xs :=
  (cpOf (fun c => !(T.is c 0x22 || T.is c 0x5C || isControlCharacter T c)) xs).or
    (seq (cp T 0x5C xs) (escape T))

/-- JSONStringCharacters? (§9): the input after the longest run of string characters. -/
def stringCharacters (xs : List α) : Opt xs :=
  match h : stringCharacter T xs with
  | some ⟨r, hr⟩ => let o := stringCharacters r; ⟨o.1, by have := o.2; omega⟩
  | none => ⟨xs, Nat.le_refl _⟩
termination_by xs.length

/-- JSONString (§9): string characters between `"` and `"`. -/
def string (xs : List α) : Rest xs :=
  seq (seqOpt (cp T 0x22 xs) (stringCharacters T)) (cp T 0x22)

mutual
/-- JSONElement (§4): a value, white space around it. -/
def element (xs : List α) : Rest xs :=
  let w := whiteSpace T xs
  match value w.1 with
  | some ⟨r, h⟩ => let o := whiteSpace T r; some ⟨o.1, by have := o.2; have := w.2; omega⟩
  | none => none
termination_by (xs.length, 3)
decreasing_by exact Prod.Lex.right' _ w.2 (by decide)

/-- JSONValue (§5). -/
def value (xs : List α) : Rest xs :=
  (object xs).or <| (array xs).or <| (number T xs).or <| (string T xs).or <|
    (cps T [0x74, 0x72, 0x75, 0x65] xs).or <| (cps T [0x66, 0x61, 0x6C, 0x73, 0x65] xs).or <|
      cps T [0x6E, 0x75, 0x6C, 0x6C] xs
termination_by (xs.length, 2)

/-- JSONObject (§6): `{` white space `}`, or `{` members `}`. -/
def object : (xs : List α) → Rest xs
  | c :: cs =>
    if !T.is c 0x7B then none
    else (lift (by simp <;> omega) (optSeq (whiteSpace T cs) (cp T 0x7D))).or <|
      match members cs with
      | some ⟨r, h⟩ => lift (by simp <;> omega) (cp T 0x7D r)
      | none => none
  | [] => none
termination_by xs => (xs.length, 0)

/-- JSONMembers (§6): members separated by `,`. -/
def members (xs : List α) : Rest xs :=
  match member xs with
  | some ⟨r, h⟩ =>
    match r, h with
    | c :: cs, h =>
      if T.is c 0x2C then
        have : cs.length < xs.length := by simp at h; omega
        match members cs with
        | some ⟨r', h'⟩ => some ⟨r', by simp at h; omega⟩
        | none => some ⟨c :: cs, h⟩
      else some ⟨c :: cs, h⟩
    | [], h => some ⟨[], h⟩
  | none => none
termination_by (xs.length, 1)

/-- JSONMember (§6): white space, a string, white space, `:`, an element. -/
def member (xs : List α) : Rest xs :=
  match seq (optSeq (whiteSpace T xs) (string T)) fun ys => optSeq (whiteSpace T ys) (cp T 0x3A) with
  | some ⟨r, h⟩ => lift (Nat.le_of_lt h) (element r)
  | none => none
termination_by (xs.length, 0)

/-- JSONArray (§7): `[` white space `]`, or `[` elements `]`. -/
def array : (xs : List α) → Rest xs
  | c :: cs =>
    if !T.is c 0x5B then none
    else (lift (by simp <;> omega) (optSeq (whiteSpace T cs) (cp T 0x5D))).or <|
      match elements cs with
      | some ⟨r, h⟩ => lift (by simp <;> omega) (cp T 0x5D r)
      | none => none
  | [] => none
termination_by xs => (xs.length, 0)

/-- JSONElements (§7): elements separated by `,`. -/
def elements (xs : List α) : Rest xs :=
  match element xs with
  | some ⟨r, h⟩ =>
    match r, h with
    | c :: cs, h =>
      if T.is c 0x2C then
        have : cs.length < xs.length := by simp at h; omega
        match elements cs with
        | some ⟨r', h'⟩ => some ⟨r', by simp at h; omega⟩
        | none => some ⟨c :: cs, h⟩
      else some ⟨c :: cs, h⟩
    | [], h => some ⟨[], h⟩
  | none => none
termination_by (xs.length, 4)
end

/-- JSONText (§4): whether `xs` is an element and nothing more. -/
def text (xs : List α) : Bool :=
  match element T xs with
  | some ⟨[], _⟩ => true
  | _ => false

end Engine.JsonText
