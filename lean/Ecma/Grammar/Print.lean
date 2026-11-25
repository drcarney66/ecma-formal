module

public import Ecma.Grammar.Core

@[expose] public section

/-!
# The grammar data, printed in spec.html's notation

`Block.printExact` prints a definition block as spec.html writes it between its tags
(grammarkdown, ECMA-262 §5.1.6): its rules at their indentation, the characters spec.html
writes by reference written so. `ecma-print` prints every block of `Gen.blocks` and every
reading of a rule, and `scripts/bijection.py` compares each with spec.html's text, and the
overlay's, byte for byte (docs/parser/GRAMMAR.md, "Round trip"): what is trusted of the
generated grammar is what a reader checks, that it prints as the specification's grammar.
-/

namespace Ecma.Grammar

def CodePointName.name : CodePointName → String
  | .TAB => "TAB"
  | .VT => "VT"
  | .FF => "FF"
  | .ZWNBSP => "ZWNBSP"
  | .USP => "USP"
  | .LF => "LF"
  | .CR => "CR"
  | .LS => "LS"
  | .PS => "PS"

/-- The code point names, by name. -/
def CodePointName.names : List (String × CodePointName) :=
  [.TAB, .VT, .FF, .ZWNBSP, .USP, .LF, .CR, .LS, .PS].map fun n => (n.name, n)

/-- The characters spec.html's grammar text writes by reference. -/
def charRefs : List (Char × String) :=
  [('<', "&lt;"), ('>', "&gt;"), ('&', "&amp;"), ('`', "&grave;"), ('∉', "&notin;"), ('∈', "&isin;"),
   ('≤', "&le;"), ('“', "&ldquo;"), ('”', "&rdquo;")]

/-- Four upper-case hexadecimal digits. -/
def hex4 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList ((List.replicate (4 - d.length) '0' ++ d).map Char.toUpper)

/-- `s` with `charRefs`' characters by reference, `>` too unless `keepGt`, and
the other non-ASCII and control characters by number (`&#x200C;`). -/
def spellChars (keepGt : Bool) (s : String) : String :=
  String.join (s.toList.map fun c =>
    if keepGt && c == '>' then ">"
    else match charRefs.lookup c with
      | some e => e
      | none => if 32 ≤ c.toNat && c.toNat < 127 then c.toString else "&#x" ++ hex4 c.toNat ++ ";")

/-- `s` with its control characters by number (`&#x0000;`). -/
def spellControls (s : String) : String :=
  String.join (s.toList.map fun c => if c.toNat < 32 || c.toNat == 127 then "&#x" ++ hex4 c.toNat ++ ";" else c.toString)

/-- A terminal as a reader sees it (`sp` false: control characters by number),
or as spec.html spells it: characters by reference, `>` raw if `alt`; the lone
backtick ``` ``` ```, or `` `&grave;` `` if `alt`. -/
def Terminal.render (sp : Bool) : Terminal → String
  | .text "`" alt => if sp && alt then "`&grave;`" else "```"
  | .text s alt => "`" ++ (if sp then spellChars alt s else spellControls s) ++ "`"
  | .cp n => (if sp then "&lt;" else "<") ++ n.name ++ (if sp then "&gt;" else ">")

def Sign.print : Sign → String
  | .plus => "+"
  | .tilde => "~"
  | .quest => "?"

def Arg.print (a : Arg) : String := a.sign.print ++ a.param.name

/-- `Name[args]`, or a terminal. -/
def Sym.render (sp : Bool) : Sym → String
  | .t x => x.render sp
  | .nt n [] => n.name
  | .nt n args => n.name ++ "[" ++ ", ".intercalate (args.map Arg.print) ++ "]"

def LookItem.render (sp : Bool) : LookItem → String
  | .t x => x.render sp
  | .noLT => "[no LineTerminator here]"

def printSeq (sp : Bool) (s : List LookItem) : String := " ".intercalate (s.map (LookItem.render sp))

def printSet (sp : Bool) (ss : List (List LookItem)) : String :=
  "{ " ++ ", ".intercalate (ss.map (printSeq sp)) ++ " }"

def Lookahead.render (sp : Bool) : Lookahead → String
  | .eq s => "[lookahead == " ++ printSeq sp s ++ "]"
  | .ne s => "[lookahead != " ++ printSeq sp s ++ "]"
  | .mem ss => "[lookahead " ++ (if sp then "&isin;" else "∈") ++ " " ++ printSet sp ss ++ "]"
  | .notMem ss => "[lookahead " ++ (if sp then "&notin;" else "∉") ++ " " ++ printSet sp ss ++ "]"
  | .notMemNT n => "[lookahead " ++ (if sp then "&notin;" else "∉") ++ " " ++ n.name ++ "]"

def Phrase.text : Phrase → String
  | .anyCodePoint => "any Unicode code point"
  | .idStart => "any Unicode code point with the Unicode property “ID_Start”"
  | .idContinue => "any Unicode code point with the Unicode property “ID_Continue”"
  | .leadSurrogate => "any Unicode code point in the inclusive interval from U+D800 to U+DBFF"
  | .trailSurrogate => "any Unicode code point in the inclusive interval from U+DC00 to U+DFFF"
  | .mvAbove10FFFF => "the MV of |HexDigits| > 0x10FFFF"
  | .mvAtMost10FFFF => "the MV of |HexDigits| ≤ 0x10FFFF"
  | .mvLead => "the MV of |Hex4Digits| is in the inclusive interval from 0xD800 to 0xDBFF"
  | .mvTrail => "the MV of |Hex4Digits| is in the inclusive interval from 0xDC00 to 0xDFFF"
  | .mvNonSurrogate => "the MV of |Hex4Digits| is not in the inclusive interval from 0xD800 to 0xDFFF"
  | .groupNumberAtMostCount =>
    "the CapturingGroupNumber of |DecimalEscape| is ≤ CountLeftCapturingParensWithin(the |Pattern| containing |DecimalEscape|)"

def Exclusion.render (sp : Bool) : Exclusion → String
  | .sym s => s.render sp
  | .oneOf ss orSep => "one of " ++ (if orSep then " or " else " ").intercalate (ss.map (Sym.render sp))

/-- An item; spelled, a condition keeps its `>` raw and a phrase starts `&gt;`. -/
def Item.render (sp : Bool) : Item → String
  | .sym s opt => s.render sp ++ (if opt then "?" else "")
  | .lookahead l => l.render sp
  | .noLT => "[no LineTerminator here]"
  | .empty => "[empty]"
  | .butNot b ex => b.render sp ++ " but not " ++ ex.render sp
  | .onlyIf c => "[> but only if " ++ (if sp then spellChars true c.text else c.text) ++ "]"
  | .phrase p => if sp then "&gt; " ++ spellChars false p.text else "> " ++ p.text

def Guard.print (g : Guard) : String := (if g.plus then "+" else "~") ++ g.param.name

/-- An alternative's text: its guard and right-hand side, without its label
(the name of its production). -/
def Alt.render (sp : Bool) (a : Alt) : String :=
  (match a.guard with
   | [] => ""
   | gs => "[" ++ ", ".intercalate (gs.map Guard.print) ++ "] ") ++
  " ".intercalate (a.rhs.map (Item.render sp))

def Alt.renderLabeled (sp : Bool) (a : Alt) : String :=
  a.render sp ++ (match a.label with | some l => " #" ++ l | none => "")

def Colons.print : Colons → String
  | .one => ":"
  | .two => "::"
  | .three => ":::"

def Rule.heading (r : Rule) : String :=
  r.lhs.name ++ (match r.params with
    | [] => ""
    | ps => "[" ++ ", ".intercalate (ps.map Param.name) ++ "]") ++
  " " ++ r.colons.print ++ (match r.body with | .oneOf _ => " one of" | .alts _ => "")

/-- A rule's lines: its heading, then each alternative (or `one of` row)
indented by two spaces. -/
def Rule.render (sp : Bool) (r : Rule) : List String :=
  r.heading :: match r.body with
    | .alts as => as.map fun a => "  " ++ a.renderLabeled sp
    | .oneOf rows => rows.map fun row => "  " ++ " ".intercalate (row.map (Terminal.render sp))

end Ecma.Grammar
