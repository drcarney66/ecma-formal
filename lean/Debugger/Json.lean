module

@[expose] public section

/-!
# JSON for the debugger's protocol

A JSON value with integer numbers, its printer and its parser. A string holding a lone surrogate,
which a `String` cannot, is kept as its UTF-16 code units (`ustr`) and printed with the lone
surrogate as `\uXXXX`. No `Lean.*` import, so that any engine's closure can use it.
-/

namespace Debugger

/-- A JSON value; numbers are integers, objects keep their keys' order. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  /-- a string with a lone surrogate, as UTF-16 code units -/
  | ustr (us : Array UInt16)
  | arr (xs : Array Json)
  | obj (kvs : Array (String × Json))
  deriving BEq, Inhabited, Repr

namespace Json

instance : Coe String Json := ⟨.str⟩
instance : Coe Bool Json := ⟨.bool⟩
instance : Coe Int Json := ⟨.num⟩
instance {n : Nat} : OfNat Json n := ⟨.num n⟩

def nat (n : Nat) : Json := .num n

/-- An object from its fields, in order. -/
def mk (kvs : List (String × Json)) : Json := .obj kvs.toArray

/-- The value of field `k`, if this is an object with one. -/
def get? (j : Json) (k : String) : Option Json :=
  match j with
  | .obj kvs => (kvs.find? (·.1 == k)).map (·.2)
  | _ => none

def str? : Json → Option String
  | .str s => some s
  | _ => none

def int? : Json → Option Int
  | .num n => some n
  | _ => none

def nat? (j : Json) : Option Nat := j.int?.bind fun n => if n < 0 then none else some n.toNat

def bool? : Json → Option Bool
  | .bool b => some b
  | _ => none

def arr? : Json → Option (Array Json)
  | .arr xs => some xs
  | _ => none

/-- The object with field `k` set to `v` (replaced in place, else appended); a non-object as the
object of that one field. -/
def set (j : Json) (k : String) (v : Json) : Json :=
  match j with
  | .obj kvs => match kvs.findIdx? (·.1 == k) with
    | some i => .obj (kvs.set! i (k, v))
    | none => .obj (kvs.push (k, v))
  | _ => .obj #[(k, v)]

/-! Printing. -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `n < 65536` as four lower-case hex digits. -/
def hex4 (n : Nat) : String :=
  String.ofList [hexDigit (n / 4096 % 16), hexDigit (n / 256 % 16), hexDigit (n / 16 % 16), hexDigit (n % 16)]

/-- `c` inside a JSON string: quotes, backslash and controls escaped. -/
def escChar (acc : String) (c : Char) : String :=
  match c with
  | '"' => acc ++ "\\\""
  | '\\' => acc ++ "\\\\"
  | '\n' => acc ++ "\\n"
  | '\r' => acc ++ "\\r"
  | '\t' => acc ++ "\\t"
  | c => if c.toNat < 0x20 then acc ++ "\\u" ++ hex4 c.toNat else acc.push c

def quote (acc s : String) : String := (s.foldl escChar (acc.push '"')).push '"'

def isHigh (u : Nat) : Bool := 0xD800 ≤ u && u < 0xDC00
def isLow (u : Nat) : Bool := 0xDC00 ≤ u && u < 0xE000

/-- Code units inside a JSON string: pairs as their code point, a lone surrogate as `\uXXXX`. -/
def quoteUnits (acc : String) (us : Array UInt16) : String :=
  let rec go (acc : String) (i : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      if h : i < us.size then
        let u := us[i].toNat
        let l := (us[i + 1]?).map (·.toNat)
        if isHigh u && (l.map isLow).getD false then
          go (escChar acc (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l.getD 0 - 0xDC00)))) (i + 2) f
        else if isHigh u || isLow u then go (acc ++ "\\u" ++ hex4 u) (i + 1) f
        else go (escChar acc (Char.ofNat u)) (i + 1) f
      else acc
  (go (acc.push '"') 0 us.size).push '"'

/-- `j` written after `acc`, on one line. -/
partial def write (acc : String) : Json → String
  | .null => acc ++ "null"
  | .bool b => acc ++ (if b then "true" else "false")
  | .num n => acc ++ toString n
  | .str s => quote acc s
  | .ustr us => quoteUnits acc us
  | .arr xs =>
    let (acc, _) := xs.foldl (fun (acc, first) x => (write (if first then acc else acc.push ',') x, false)) (acc.push '[', true)
    acc.push ']'
  | .obj kvs =>
    let (acc, _) := kvs.foldl (fun (acc, first) (k, v) =>
      (write ((quote (if first then acc else acc.push ',') k).push ':') v, false)) (acc.push '{', true)
    acc.push '}'

/-- `j` on one line. -/
def render (j : Json) : String := write "" j

/-- UTF-16 code units as a string value: `str` unless a surrogate is lone. -/
def ofUnits (us : Array UInt16) : Json :=
  let rec go (i : Nat) (acc : String) (fuel : Nat) : Option String :=
    match fuel with
    | 0 => some acc
    | f + 1 =>
      if h : i < us.size then
        let u := us[i].toNat
        if isHigh u then match us[i + 1]? with
          | some l => if isLow l.toNat then
              go (i + 2) (acc.push (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l.toNat - 0xDC00)))) f
            else none
          | none => none
        else if isLow u then none
        else go (i + 1) (acc.push (Char.ofNat u)) f
      else some acc
  match go 0 "" us.size with
  | some s => .str s
  | none => .ustr us

/-! Parsing. -/

def fail {α : Type} (i : Nat) (what : String) : Except String (α × Nat) := .error s!"at {i}: {what}"

/-- The index of the first non-blank character from `i`. -/
partial def skipWs (cs : Array Char) (i : Nat) : Nat :=
  match cs[i]? with
  | some ' ' | some '\n' | some '\r' | some '\t' => skipWs cs (i + 1)
  | _ => i

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def hex4At (cs : Array Char) (i : Nat) : Option Nat := do
  let d ← [0, 1, 2, 3].mapM fun k => cs[i + k]? >>= hexVal
  return d.foldl (fun n x => n * 16 + x) 0

/-- A char's UTF-16 code units, pushed. -/
def pushUnits (us : Array UInt16) (c : Char) : Array UInt16 :=
  let n := c.toNat
  if n < 0x10000 then us.push n.toUInt16
  else us.push (0xD800 + (n - 0x10000) / 0x400).toUInt16 |>.push (0xDC00 + (n - 0x10000) % 0x400).toUInt16

/-- A string's contents from `i` (after its opening quote), as code units. -/
partial def strUnits (cs : Array Char) (i : Nat) (us : Array UInt16) : Except String (Array UInt16 × Nat) :=
  match cs[i]? with
  | none => fail i "unterminated string"
  | some '"' => .ok (us, i + 1)
  | some '\\' => match cs[i + 1]? with
    | some '"' => strUnits cs (i + 2) (us.push 0x22)
    | some '\\' => strUnits cs (i + 2) (us.push 0x5C)
    | some '/' => strUnits cs (i + 2) (us.push 0x2F)
    | some 'b' => strUnits cs (i + 2) (us.push 0x08)
    | some 'f' => strUnits cs (i + 2) (us.push 0x0C)
    | some 'n' => strUnits cs (i + 2) (us.push 0x0A)
    | some 'r' => strUnits cs (i + 2) (us.push 0x0D)
    | some 't' => strUnits cs (i + 2) (us.push 0x09)
    | some 'u' => match hex4At cs (i + 2) with
      | some n => strUnits cs (i + 6) (us.push n.toUInt16)
      | none => fail (i + 2) "bad \\u escape"
    | _ => fail (i + 1) "bad escape"
  | some c => if c.toNat < 0x20 then fail i "control character in string" else strUnits cs (i + 1) (pushUnits us c)

def string (cs : Array Char) (i : Nat) : Except String (Json × Nat) := do
  let (us, j) ← strUnits cs i #[]
  return (ofUnits us, j)

def stringKey (cs : Array Char) (i : Nat) : Except String (String × Nat) := do
  let (us, j) ← strUnits cs i #[]
  match ofUnits us with
  | .str s => return (s, j)
  | _ => fail i "lone surrogate in a key"

partial def digits (cs : Array Char) (i : Nat) (n : Nat) : Nat × Nat :=
  match cs[i]? with
  | some c => if '0' ≤ c && c ≤ '9' then digits cs (i + 1) (n * 10 + (c.toNat - 48)) else (n, i)
  | none => (n, i)

def number (cs : Array Char) (i : Nat) : Except String (Json × Nat) :=
  let neg := cs[i]? == some '-'
  let s := if neg then i + 1 else i
  match cs[s]? with
  | some c =>
    if !('0' ≤ c && c ≤ '9') then fail s "expected a digit"
    else
      let (n, j) := digits cs s 0
      if c == '0' && j > s + 1 then fail s "leading zero"
      else match cs[j]? with
        | some '.' | some 'e' | some 'E' => fail j "only integers"
        | _ => .ok (.num (if neg then -(n : Int) else n), j)
  | none => fail s "expected a digit"

def literal (cs : Array Char) (i : Nat) (word : String) (v : Json) : Except String (Json × Nat) :=
  if (word.toList.zipIdx.all fun (c, k) => cs[i + k]? == some c) then .ok (v, i + word.length)
  else fail i s!"expected {word}"

mutual
partial def value (cs : Array Char) (i : Nat) : Except String (Json × Nat) :=
  let i := skipWs cs i
  match cs[i]? with
  | some '{' => object cs (skipWs cs (i + 1)) #[]
  | some '[' => array cs (skipWs cs (i + 1)) #[]
  | some '"' => string cs (i + 1)
  | some 't' => literal cs i "true" (.bool true)
  | some 'f' => literal cs i "false" (.bool false)
  | some 'n' => literal cs i "null" .null
  | some _ => number cs i
  | none => fail i "expected a value"

partial def array (cs : Array Char) (i : Nat) (xs : Array Json) : Except String (Json × Nat) :=
  if xs.isEmpty && cs[i]? == some ']' then .ok (.arr xs, i + 1)
  else do
    let (x, j) ← value cs i
    let j := skipWs cs j
    match cs[j]? with
    | some ',' => array cs (skipWs cs (j + 1)) (xs.push x)
    | some ']' => return (.arr (xs.push x), j + 1)
    | _ => fail j "expected , or ]"

partial def object (cs : Array Char) (i : Nat) (kvs : Array (String × Json)) : Except String (Json × Nat) :=
  if kvs.isEmpty && cs[i]? == some '}' then .ok (.obj kvs, i + 1)
  else if cs[i]? != some '"' then fail i "expected a key"
  else do
    let (k, j) ← stringKey cs (i + 1)
    let j := skipWs cs j
    if cs[j]? != some ':' then throw s!"at {j}: expected :"
    let (v, j) ← value cs (j + 1)
    let j := skipWs cs j
    match cs[j]? with
    | some ',' => object cs (skipWs cs (j + 1)) (kvs.push (k, v))
    | some '}' => return (.obj (kvs.push (k, v)), j + 1)
    | _ => fail j "expected , or }"
end

/-- The one value `s` holds, blanks around it allowed. -/
def parse (s : String) : Except String Json := do
  let cs := s.toList.toArray
  let (v, i) ← value cs 0
  let i := skipWs cs i
  if i < cs.size then .error s!"at {i}: trailing characters" else return v

end Json

end Debugger
