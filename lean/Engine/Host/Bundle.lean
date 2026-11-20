module

@[expose] public section

/-!
# V8's single-file bundles (`d8 --bundle`)

A bundle is one source file that carries scripts and a module graph, as d8's `TryExecuteBundle`
(src/d8/d8.cc at external/js/v8's pin) reads it:

- The header: whitespace (C's `isspace`), `//` comments each up to its newline and `/* */`
  comments, up to the first line that starts `// JS_BUNDLE_` (one space). Any other text, a `//`
  comment without a newline after it, an unclosed `/*`, or no marker: the file is not a bundle,
  and d8 runs it as a Script.
- From each marker the marker's line (up to `\n`, one `\r` before it dropped) and the part, the text
  after that line up to the next `// JS_BUNDLE_` anywhere (not only at a line's start) or the end,
  read up to its first NUL (d8 makes its source by `c_str`):
  `// JS_BUNDLE_SCRIPT` exactly, a Script; `// JS_BUNDLE_MODULE:NAME`, the module NAME (NAME the
  rest of the line, untrimmed); `// JS_BUNDLE_MODULE_ENTRYPOINT:NAME`, the module NAME and an
  entrypoint, `// JS_BUNDLE_MODULE_ENTRYPOINT` followed by anything but `:`, the entrypoint
  `entrypoint_N.mjs` (N counting them from 0); another marker, a warning, its part dropped.
- A module's key is its name as d8 normalizes it against the working directory (`keyOf`); a second
  module of one key is an error (`Duplicate bundle module: KEY`).

A specifier resolves as d8 resolves it (`resolve`): `data:text/javascript,`, `http://` and
`https://` ones are keys as they are; any other is a path (a bare `a.mjs` as `./a.mjs`) against
the directory of its referrer's key, or of the working directory for a Script, a Realm or a key
that is not a path, `\` read as `/`, `.` and empty segments dropped and `..` dropping the one
before.

Differences from d8: the working directory is the root (the key of `a.mjs` is `/a.mjs`, and `..`
never leaves it); what runs is one entrypoint, after the scripts before it (`plan`: no entrypoint,
two, or a script after it are errors where d8 runs every item in order); a key the bundle lacks
loads nothing (the host's TypeError: d8 reads the file system or the data URL); warnings go to
stderr.

`write` makes a bundle of a directory's modules, the entry module last.
-/

namespace Engine.Host.Bundle

/-- What starts every marker. -/
def markerPrefix : List Char := "// JS_BUNDLE_".toList

def scriptMarker : String := "// JS_BUNDLE_SCRIPT"

def modulePrefix : String := "// JS_BUNDLE_MODULE:"

def entryPrefix : String := "// JS_BUNDLE_MODULE_ENTRYPOINT"

/-- C's `isspace` in the C locale. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c.toNat == 0x0B || c.toNat == 0x0C || c == '\r'

/-- The text up to and with the first `\n`, and the rest; none without one. -/
def splitLine : List Char → Option (List Char × List Char)
  | [] => none
  | '\n' :: r => some (['\n'], r)
  | c :: r => (splitLine r).map fun (a, b) => (c :: a, b)

/-- The text up to and with the first `*/`, and the rest; none without one. -/
def splitBlock : List Char → Option (List Char × List Char)
  | [] => none
  | '*' :: '/' :: r => some (['*', '/'], r)
  | c :: r => (splitBlock r).map fun (a, b) => (c :: a, b)

/-- The header and the text from the first marker on (`fuel` past the text's length); none: not a
bundle. -/
def splitHeader : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, cs@(c :: r) =>
    let more := fun (a b : List Char) => (splitHeader f b).map fun (h, t) => (a ++ h, t)
    if isSpace c then more [c] r
    else match cs with
      | '/' :: '/' :: _ =>
        if markerPrefix.isPrefixOf cs then some ([], cs)
        else (splitLine cs).bind fun (a, b) => more a b
      | '/' :: '*' :: r' => (splitBlock r').bind fun (a, b) => more ('/' :: '*' :: a) b
      | _ => none

/-- The text up to the next marker, and the text from it. -/
def untilMarker : List Char → List Char × List Char
  | [] => ([], [])
  | cs@(c :: r) =>
    if markerPrefix.isPrefixOf cs then ([], cs)
    else let (a, b) := untilMarker r; (c :: a, b)

/-- A marker's line (one `\r` before its `\n` dropped) and the text after it. -/
def markerLine (cs : List Char) : List Char × List Char :=
  match splitLine cs with
  | some (l, r) =>
    let l := l.dropLast
    (if l.getLast? == some '\r' then l.dropLast else l, r)
  | none => (cs, [])

/-- The marker lines and their parts (`fuel` past the text's length). -/
def parts : Nat → List Char → List (String × String)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, cs =>
    let (h, r) := markerLine cs
    let (t, r) := untilMarker r
    (String.ofList h, String.ofList (t.takeWhile (· != '\x00'))) :: parts f r

/-! Keys and specifiers. -/

/-- The working directory: the root. -/
def cwd : String := ""

/-- d8's NormalizePath: `path` against the directory `dir` (unless absolute), `\` read as `/`, `.`
and empty segments dropped and `..` dropping the one before. -/
def normalizePath (path dir : String) : String :=
  let abs := if path.startsWith "/" then path else dir ++ "/" ++ path
  let abs := String.ofList (abs.toList.map fun c => if c == '\\' then '/' else c)
  let segs := (abs.splitOn "/").foldl (init := ([] : List String)) fun acc s =>
    if s == ".." then acc.dropLast else if s == "" || s == "." then acc else acc ++ [s]
  "/" ++ "/".intercalate segs

/-- d8's NormalizeModuleSpecifier: a data URL or an `http://` or `https://` URL as it is, else a path
(`normalizePath`). -/
def normalizeSpecifier (spec dir : String) : String :=
  if spec.startsWith "data:text/javascript," || spec.startsWith "http://" || spec.startsWith "https://" then spec
  else normalizePath spec dir

/-- d8's DirName: an absolute path's directory (without its last `/`), else the working directory. -/
def dirName (path : String) : String :=
  if path.startsWith "/" then String.ofList ((path.toList.reverse.dropWhile (· != '/')).drop 1).reverse
  else cwd

/-- The key of the module a bundle names `name`. -/
def keyOf (name : String) : String := normalizeSpecifier name cwd

/-- The key of `spec` imported by the module of the key `base` (none: a Script or a Realm). -/
def resolve (base : Option String) (spec : String) : String :=
  normalizeSpecifier spec ((base.map dirName).getD cwd)

/-- UTF-16 code units as a String, a lone surrogate as U+FFFD. -/
def ofUnits (u : Array UInt16) : String := Id.run do
  let mut out : List Char := []
  let mut j := 0
  while j < u.size do
    let a := u[j]!.toNat
    let b := (u[j + 1]?.map (·.toNat)).getD 0
    if 0xD800 ≤ a && a < 0xDC00 && 0xDC00 ≤ b && b < 0xE000 then
      out := Char.ofNat (0x10000 + (a - 0xD800) * 0x400 + (b - 0xDC00)) :: out
      j := j + 2
    else
      out := Char.ofNat (if 0xD800 ≤ a && a < 0xE000 then 0xFFFD else a) :: out
      j := j + 1
  return String.ofList out.reverse

/-! Bundles. -/

/-- What a bundle runs, in order: a Script's text, or the entrypoint of a key. -/
inductive Item where
  | script (text : String)
  | entry (key : String)
  deriving BEq, Repr

/-- A bundle: its header, its modules (the name its marker gives, the key, the text) in order, what
it runs, and the warnings of its unknown markers. -/
structure Bundle where
  header : String
  modules : List (String × String × String) := []
  items : List Item := []
  warnings : List String := []
  deriving BEq, Repr

/-- The module sources by key. -/
def Bundle.table (b : Bundle) : List (String × String) := b.modules.map fun (_, k, t) => (k, t)

/-- The module of `name` and text `t` added; error: its key is another's. -/
def Bundle.add (b : Bundle) (name t : String) : Except String Bundle :=
  let k := keyOf name
  if b.modules.any (·.2.1 == k) then .error s!"Duplicate bundle module: {k}"
  else .ok { b with modules := b.modules ++ [(name, k, t)] }

/-- A marker line and its part read into `b`; `anon`: the anonymous entrypoints so far. -/
def Bundle.part (b : Bundle × Nat) (p : String × String) : Except String (Bundle × Nat) :=
  let (b, anon) := b
  let (h, t) := p
  if h == scriptMarker then .ok ({ b with items := b.items ++ [.script t] }, anon)
  else if h.startsWith modulePrefix then
    return (← b.add (String.ofList (h.toList.drop modulePrefix.length)) t, anon)
  else if h.startsWith entryPrefix then
    let rest := h.toList.drop entryPrefix.length
    let (name, anon') := match rest with
      | ':' :: n => (String.ofList n, anon)
      | _ => (s!"entrypoint_{anon}.mjs", anon + 1)
    return ({ ← b.add name t with items := b.items ++ [.entry (keyOf name)] }, anon')
  else .ok ({ b with warnings := b.warnings ++ [s!"Unknown bundle marker: {h}"] }, anon)

/-- The bundle `text` is, as d8 reads it; none: not a bundle; error: a duplicate module. -/
def parse (text : String) : Except String (Option Bundle) :=
  let cs := text.toList
  match splitHeader (cs.length + 1) cs with
  | none => .ok none
  | some (h, rest) =>
    some <$> (·.1) <$> (parts (rest.length + 1) rest).foldlM Bundle.part ({ header := String.ofList h }, 0)

/-- What runs: the scripts before the one entrypoint, its key and text; error: no entrypoint, two,
or a script after it. -/
def Bundle.plan (b : Bundle) : Except String (List String × String × String) :=
  match b.items.findIdx? (· matches .entry _) with
  | none => .error "no JS_BUNDLE_MODULE_ENTRYPOINT"
  | some i =>
    let after := b.items.drop (i + 1)
    if after.any (· matches .entry _) then .error "more than one JS_BUNDLE_MODULE_ENTRYPOINT"
    else if after.any (· matches .script _) then .error "a JS_BUNDLE_SCRIPT after the entrypoint"
    else match b.items[i]? with
      | some (.entry k) =>
        let scripts := (b.items.take i).filterMap fun | .script t => some t | _ => none
        .ok (scripts, k, ((b.table.lookup k).getD ""))
      | _ => .error "no JS_BUNDLE_MODULE_ENTRYPOINT"

/-! Writing a bundle. -/

/-- The header `write` gives a bundle: V8's test runner's flag. -/
def writtenHeader : String := "// Flags: --bundle\n\n"

/-- A module's part: its marker line, then its text with a newline at its end. -/
def writePart (marker name text : String) : String :=
  marker ++ name ++ "\n" ++ text ++ (if text.isEmpty || text.endsWith "\n" then "" else "\n")

/-- The bundle of the modules `mods` (name, text) and the entry module `entry` last; error: a name
that is empty or not one line, two names of one key, or a text with a marker or a NUL in it. -/
def write (entry : String × String) (mods : List (String × String)) : Except String String := do
  let all := mods ++ [entry]
  for (n, t) in all do
    if n.isEmpty || n.contains '\n' || n.endsWith "\r" then throw s!"{n}: not a one-line name"
    if (t.splitOn (String.ofList markerPrefix)).length > 1 then throw s!"{n}: its text has a // JS_BUNDLE_ marker"
    if t.contains '\x00' then throw s!"{n}: its text has a NUL"
  let keys := all.map (keyOf ·.1)
  if keys.eraseDups.length != keys.length then throw "two modules of one key"
  return writtenHeader ++ String.join (mods.map fun (n, t) => writePart modulePrefix n t) ++
    entryPrefix ++ ":" ++ entry.1 ++ "\n" ++ entry.2

end Engine.Host.Bundle
