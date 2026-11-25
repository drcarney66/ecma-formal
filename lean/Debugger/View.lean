module

public import Debugger.Show
public import Debugger.Json
public import Ecma.Prims.Nodes
public import Std.Data.HashMap

@[expose] public section

/-!
# The debugger's views of a pause

Engine-neutral (docs/debugger/state.md §3, §4, §7): what a pause shows, built from an engine's
`FrameView`s and the `Ecma.State`, with the adapter's `Names`.

- A frame (`FrameView`): its algorithm and step (path and full text), its slots by name as the frame
  holds them (not yet bound: `unbound`, D11), its Parse Node, its kind, the run it belongs to, and an
  optional engine detail (the machine's control and continuations).
- Its scopes: "Slots", "Step" (text, detail and a link to the live draft, D12), "Node" (production,
  span, source excerpt and position) and "Execution contexts" (`State.stack` with `resumed`,
  `suspended` and what §7 derives: the running context, the active function, the current Realm,
  GetActiveScriptOrModule and the running code's strictness).
- A value whose cell the pause has shows the cell's kind as its type, and expands to the cell
  (its address + 1, `Debugger.Heap.cellVars`).
-/

namespace Debugger

open Ecma

/-- An engine's own detail of a frame: its control (what it is doing) and its continuations,
innermost first, one line each. -/
structure Detail where
  control : String
  konts : List String

/-- A frame as the debugger shows it: its algorithm (sec-id, index and name), the step it is at
(path and full text), its kind (`steps` with its `flags` rc/boundary/used, or `eval`), the index
of the run it belongs to (0 the outermost), its slots by name, its Parse Node, and the engine's
detail. -/
structure FrameView where
  alg : AlgId
  secId : String
  name : String
  path : String
  /-- the overlay id of the erratum's reading the step is in (`path` numbered within it) -/
  reading : Option String := none
  text : String
  spectec : String := ""
  kind : String
  run : Nat
  flags : List String := []
  slots : List (String × Val F) := []
  node : Option F.Node := none
  detail : Option Detail := none

def isLineTerminator (c : Nat) : Bool := c == 0x0A || c == 0x0D || c == 0x2028 || c == 0x2029

/-- Where each line of `src` starts; CR LF is one line terminator. -/
def lineStartsOf (src : Array Nat) : Array Nat := Id.run do
  let mut starts := #[0]
  for j in [0:src.size] do
    let c := src[j]!
    if isLineTerminator c && !(c == 0x0D && src[j + 1]? == some 0x0A) then
      starts := starts.push (j + 1)
  return starts

/-- A source a session shows, the program or eval or Function code: its path (none for a `source`
or code parsed by the run), its code points, the stamp of its parse, which its Parse Nodes carry,
where its lines start, the parses of its text (its own and the reparses of its nodes, by stamp)
with their offsets in its parse's input, where its text starts in that input (`shift`: its root node's
start), its root node, and for code parsed by the run or a bundle's module its name and DAP
`sourceReference` (0 for the program, whose name is a bundle's entry module's). -/
structure Program where
  path : Option String
  src : Array Nat
  stamp : Nat
  lineStarts : Array Nat := lineStartsOf src
  origins : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert stamp 0
  shift : Nat := 0
  root : Option F.Node := none
  name : String := ""
  ref : Nat := 0

/-- The sources: the program first (if any), then the code parsed after `arm` in the order parsed;
each parse of their texts' source, by stamp, as an index into `all`. -/
structure Sources where
  all : Array Program := #[]
  owner : Std.HashMap Nat Nat := {}

/-- The sources with only the program. -/
def Sources.ofProgram : Option Program → Sources
  | some p => { all := #[p], owner := p.origins.fold (init := {}) fun m k _ => m.insert k 0 }
  | none => {}

/-- `p` added as the last source. -/
def Sources.add (s : Sources) (p : Program) : Sources :=
  { all := s.all.push p, owner := p.origins.fold (init := s.owner) fun m k _ => m.insert k s.all.size }

/-- The parse `k` of source `i`'s text, at offset `o` in it. -/
def Sources.addOrigin (s : Sources) (i k o : Nat) : Sources :=
  { all := s.all.modify i fun p => { p with origins := p.origins.insert k o }, owner := s.owner.insert k i }

def Sources.program (s : Sources) : Option Program := s.all[0]?.filter (·.ref == 0)

/-- The source of the parse `k`, if it is of one's text. -/
def Sources.of? (s : Sources) (k : Nat) : Option Program := (s.owner.get? k).bind (s.all[·]?)

/-- Whether the parse `k` is of a source's text. -/
@[inline] def Sources.knows (s : Sources) (k : Nat) : Bool := s.owner.contains k

/-- The source of a `sourceReference` (0: the program). -/
def Sources.byRef? (s : Sources) (ref : Nat) : Option Program :=
  if ref == 0 then s.program else s.all.find? (·.ref == ref)

/-- Code points as a String, a surrogate as U+FFFD. -/
def pointsText (src : Array Nat) : String :=
  String.ofList (src.toList.map fun c => if 0xD800 ≤ c && c < 0xE000 then Char.ofNat 0xFFFD else Char.ofNat c)

/-- A pause: the frames (innermost first, built on demand), the state (none at a stop, whose state
the run no longer has), the depth, the step entered and the stop's name. -/
structure Paused where
  frames : Unit → List FrameView
  state : Option (State F)
  depth : Nat
  entered : Option (AlgId × List Nat)
  stop? : Option String := none
  /-- the contexts on the stack when the outermost frames' run started -/
  base : Nat := 0

/-! Source positions. -/

/-- The 1-based line and column (in code points) of position `i`, by the line starts `starts`. -/
def lineCol (starts : Array Nat) (i : Nat) : Nat × Nat :=
  -- the last start ≤ i, in [lo, hi)
  let rec go (lo hi : Nat) (fuel : Nat) : Nat := match fuel with
    | 0 => lo
    | f + 1 =>
      if hi ≤ lo + 1 then lo
      else
        let mid := (lo + hi) / 2
        if starts[mid]! ≤ i then go mid hi f else go lo mid f
  let k := go 0 starts.size 64
  (k + 1, i - starts[k]! + 1)

def nodeStamp : F.Node → Nat
  | .mk k .. => k

def nodeSpan : F.Node → Nat × Nat
  | .mk _ lo hi .. => (lo, hi)

def nodeText : F.Node → Array UInt16
  | .mk _ _ _ _ _ _ _ t => Engine.Model.unitsOf t.toArray

def nodePoints : F.Node → Array Nat
  | .mk _ _ _ _ _ _ _ t => t.toArray

/-- The first `sourceReference` of a bundle's modules (above every parse's stamp + 1). -/
def moduleRefBase : Nat := 2 ^ 30

/-- A bundle's sources: the program `p` as its entry module (key `key`) under the name its marker
gives, and each other module (name, key, text) a source of its own (`moduleRefBase + i`) with no
parse until `Sources.adopt`. -/
def bundlePrograms (p : Program) (key : String) (mods : List (String × String × String)) :
    Program × List Program :=
  let others := (mods.filter (·.2.1 != key)).zipIdx.map fun ((n, _, t), i) =>
    { path := none, src := (t.toList.map Char.toNat).toArray, stamp := 0, origins := {}, name := n,
      ref := moduleRefBase + i : Program }
  ({ p with name := ((mods.find? (·.2.1 == key)).map (·.1)).getD p.name }, others)

/-- The parse `k` of source `i`'s whole text (its root `root`) as its own. -/
def Sources.adopt (s : Sources) (i k : Nat) (root : F.Node) : Sources :=
  let own : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert k 0
  let set := fun (p : Program) => { p with stamp := k, origins := own, root := some root }
  { all := s.all.modify i set, owner := s.owner.insert k i }

/-- The offset in the source's text of offset `lo` in the parse `k`'s input. -/
@[inline] def Program.offset (p : Program) (k lo : Nat) : Nat := p.origins.getD k 0 + lo - p.shift

/-- The node's span in the source's text, if its parse is of that text. -/
def Program.spanIn? (p : Program) (n : F.Node) : Option (Nat × Nat) :=
  (p.origins.get? (nodeStamp n)).map fun o => (o + (nodeSpan n).1 - p.shift, o + (nodeSpan n).2 - p.shift)

/-- The node's position in the program, if its parse is of the program's text. -/
def Program.at? (p : Program) (n : F.Node) : Option (Nat × Nat) :=
  (p.spanIn? n).map fun (lo, _) => lineCol p.lineStarts lo

/-! Frames in `stackTrace`. -/

/-- The program's file name: the last component of its path. -/
def baseName (path : String) : String := ((path.splitOn "/").getLast?).getD path

/-- The source as a DAP `source`: code parsed by the run by its `sourceReference`. -/
def Program.sourceJson (p : Program) : Json :=
  if p.ref != 0 then Json.mk [("name", p.name), ("sourceReference", .nat p.ref)]
  else match p.path with
  | some path => Json.mk [("name", if p.name.isEmpty then baseName path else p.name), ("path", path)]
  | none => Json.mk [("name", if p.name.isEmpty then "source" else p.name)]

/-- The node's source, if its parse is of a source's text. -/
def Sources.ofNode? (s : Sources) (n : F.Node) : Option Program := s.of? (nodeStamp n)

def FrameView.json (n : Names) (srcs : Sources) (f : FrameView) (id : Nat) : Json :=
  let pos := f.node.bind fun nd => (srcs.ofNode? nd).bind fun p => (p.spanIn? nd).map fun sp => (p, sp)
  let spec := Json.mk [("secId", f.secId), ("idx", .nat f.alg.idx), ("path", f.path), ("text", f.text),
    ("spectec", f.spectec), ("kind", f.kind), ("run", .nat f.run)]
  let spec := match f.reading with
    | some r => spec.set "reading" r
    | none => spec
  let spec := if f.flags.isEmpty then spec else spec.set "flags" (.arr (f.flags.map Json.str).toArray)
  let spec := match f.node with
    | some nd@(.mk _ _ _ prod nt _ _ _) => spec.set "node" (Json.mk [("production", Show.prodText n nt prod), ("lo", .nat (nodeSpan nd).1),
        ("hi", .nat (nodeSpan nd).2)])
    | none => spec
  let base := [("id", Json.nat id), ("name", .str f.name)]
  let loc : List (String × Json) := match pos with
    | some (p, (lo, hi)) =>
      let ((l, c), (el, ec)) := (lineCol p.lineStarts lo, lineCol p.lineStarts hi)
      [("source", p.sourceJson), ("line", .nat l), ("column", .nat c), ("endLine", .nat el), ("endColumn", .nat ec),
        ("lo", .nat lo), ("hi", .nat hi)]
    | none => [("line", 0), ("column", 0)]
  Json.mk (base ++ loc ++ [("spec", spec)])

/-! Listings. -/

partial def ListingStep.json (s : ListingStep) : Json :=
  let j := Json.mk [("path", s.path), ("text", s.text), ("spectec", s.spectec), ("depth", .nat s.depth)]
  let j := match s.reading with
    | some r => j.set "reading" r
    | none => j
  if s.steps.isEmpty then j else j.set "steps" (.arr (s.steps.map ListingStep.json).toArray)

def Listing.json (l : Listing) : Json :=
  let j := Json.mk [("name", l.name), ("secId", l.secId), ("idx", .nat l.idx), ("kind", l.kind),
    ("spectecHead", l.spectecHead)]
  let j := match l.production with
    | some p => j.set "production" p
    | none => j
  (j.set "params" (.arr (l.params.map Json.str).toArray)).set "steps" (.arr (l.steps.map ListingStep.json).toArray)

/-! Variables. -/

/-- A variable as `variables` lists it: its name, value, type, reference (0: none), its
elements' count where it is a List, and its presentation attributes (`changed`). -/
structure Var where
  name : String
  value : Json
  type : String := ""
  ref : Nat := 0
  indexed : Option Nat := none
  attrs : List String := []

def Var.json (v : Var) : Json :=
  let j := Json.mk [("name", v.name), ("value", v.value), ("type", v.type), ("variablesReference", .nat v.ref)]
  let j := match v.indexed with
    | some k => j.set "indexedVariables" (.nat k)
    | none => j
  if v.attrs.isEmpty then j else j.set "presentationHint" (Json.mk [("attributes", .arr (v.attrs.map Json.str).toArray)])

/-- A value as a variable. -/
def valVar (n : Names) (name : String) (v : Val F) (type : String := Show.type v) : Var :=
  { name, value := Show.val n v, type, ref := Show.ref v }

/-- Where scope references start; below it a reference is a cell's address + 1. -/
def scopeBase : Nat := 2 ^ 44

inductive ScopeKind where
  | slots | step | node | contexts | konts

def ScopeKind.idx : ScopeKind → Nat
  | .slots => 0 | .step => 1 | .node => 2 | .contexts => 3 | .konts => 4

def ScopeKind.ofIdx? : Nat → Option ScopeKind
  | 0 => some .slots | 1 => some .step | 2 => some .node | 3 => some .contexts | 4 => some .konts
  | _ => none

def scopeRef (frame : Nat) (k : ScopeKind) : Nat := scopeBase + 8 * frame + k.idx

/-- A reference's frame and scope, or its cell's address. -/
def decodeRef (r : Nat) : Option (Nat × ScopeKind) ⊕ Nat :=
  if r ≥ scopeBase then .inl ((ScopeKind.ofIdx? ((r - scopeBase) % 8)).map ((r - scopeBase) / 8, ·))
  else .inr (r - 1)

/-- The live draft's section for a sec-id (D12: the pinned text is the step text shown). -/
def specLink (secId : String) : String := "https://tc39.es/ecma262/#" ++ secId

def stepVars (f : FrameView) (id : Nat) : List Var :=
  let kind := " ".intercalate (f.kind :: f.flags)
  [{ name := "text", value := f.text }, { name := "algorithm", value := f.name },
    { name := "secId", value := f.secId }] ++
  (f.reading.map fun r => { name := "reading", value := r, type := "an erratum's reading; path within it" : Var }).toList ++
  [{ name := "path", value := f.path }, { name := "kind", value := kind }, { name := "run", value := toString f.run },
    { name := "link", value := specLink f.secId, type := "live draft; may differ from the pinned text" }] ++
  match f.detail with
  | some d =>
    [{ name := "control", value := d.control },
      { name := "continuations", value := s!"{d.konts.length}", ref := if d.konts.isEmpty then 0 else scopeRef id .konts }]
  | none => []

def kontVars (f : FrameView) : List Var :=
  match f.detail with
  | some d => d.konts.zipIdx.map fun (k, i) => { name := toString i, value := k }
  | none => []

/-- The `scopes` of frame `id`: Slots, Step, Node (if the frame has one), Execution contexts
(if the pause has the state). -/
def scopes (f : FrameView) (id : Nat) (hasState : Bool) : Json :=
  let one := fun (name : String) (k : ScopeKind) (hint : Option String) (count : Option Nat) =>
    let j := Json.mk [("name", name), ("variablesReference", .nat (scopeRef id k)), ("expensive", false)]
    let j := match count with
      | some c => j.set "namedVariables" (.nat c)
      | none => j
    match hint with
    | some h => j.set "presentationHint" h
    | none => j
  let ss := [one "Slots" .slots (some "locals") (some f.slots.length), one "Step" .step none (some (stepVars f id).length)]
  let ss := if f.node.isSome then ss ++ [one "Node" .node none none] else ss
  let ss := if hasState then ss ++ [one "Execution contexts" .contexts none none] else ss
  Json.mk [("scopes", .arr ss.toArray)]

def nodeVars (n : Names) (srcs : Sources) (nd : F.Node) : List Var :=
  let .mk stamp lo hi p nt _ _ text := nd
  let pos := match (srcs.ofNode? nd).bind fun pr => (pr.at? nd).map (pr, ·) with
    | some (pr, (l, c)) =>
      (if pr.ref != 0 then [{ name := "source", value := pr.name : Var }] else []) ++
        [{ name := "line", value := toString l }, { name := "column", value := toString c : Var }]
    | none => match srcs.program with
      | some pr => [{ name := "source", value := s!"parse {stamp}, not of a source's text (the program's is {pr.stamp})" }]
      | none => []
  [{ name := "production", value := Show.prodText n nt p }, { name := "nonterminal", value := n.nt nt },
    { name := "span", value := s!"[{lo}, {hi})" }, { name := "lo", value := toString lo }, { name := "hi", value := toString hi },
    { name := "parse", value := toString stamp }, { name := "excerpt", value := .ustr (Engine.Model.unitsOf text), type := "source text" }] ++ pos

/-! Execution contexts (state.md §7, state-internal.md §3.3). -/

def cell? (s : State F) (a : Nat) : Option (Cell F) := F.heapGet s.heap a

/-- A Record's field. -/
def fieldOf (s : State F) (v : Val F) (f : FieldId) : Option (Val F) :=
  match v with
  | .ref a | .obj a => match cell? s (Show.addr a) with
    | some (.record _ fs) | some (.env _ fs _) | some (.object fs _) => F.recGet fs f
    | _ => none
  | _ => none

/-- A cell's kind, as a `type`. -/
def cellType (n : Names) (s : State F) (v : Val F) : String :=
  match v with
  | .ref a | .obj a => match cell? s (Show.addr a) with
    | some (.record k _) => n.sort k
    | some (.env k _ _) => n.sort k
    | some (.list xs _) => s!"List ({xs.size})"
    | some (.block bs) => s!"Data Block ({bs.size})"
    | some (.charSet cs) => s!"CharSet ({(Engine.Model.MathVal.idx (F.csSize cs)).getD 0})"
    | some (.object ..) => "Object"
    | none => "(no cell)"
  | v => Show.type v

/-- A value as a variable: its cell's kind as its type, a List's length as its indexed count. -/
def cellVar (n : Names) (s : State F) (name : String) (v : Val F) : Var :=
  let indexed := match v with
    | .ref a => match cell? s (Show.addr a) with
      | some (.list xs _) => some xs.size
      | some (.block bs) => some bs.size
      | some (.charSet cs) => Engine.Model.MathVal.idx (F.csSize cs)
      | _ => none
    | _ => none
  { valVar n name v (cellType n s v) with indexed }

def stackList (s : State F) : List (Val F) := s.stack.toList

/-- §9.4.1 GetActiveScriptOrModule: the ScriptOrModule of the topmost context with one, else null. -/
def activeScriptOrModule (s : State F) : Val F :=
  (stackList s).foldl (fun r ctx => match fieldOf s ctx Known.fScriptOrModule with
    | some .null | none => r
    | some v => v) .null

def nodeKids : F.Node → List F.Node
  | .mk _ _ _ _ _ _ kids _ => kids.toList.filterMap (·.2)

def nodeNt : F.Node → NtId
  | .mk _ _ _ _ nt _ _ _ => nt

/-- The running code's strictness (§11.2.2), and how it was found: the active function's
[[Strict]] (a built-in function has none), a Module's code, eval code parsed as strict from
outside, or the Use Strict Directive of the code's parse (the innermost frame's Parse Node, through
`State.roots`). -/
def strictness (n : Names) (s : State F) (running : Option (Val F)) (frames : List FrameView) : String :=
  let fn := running.bind fun ctx => fieldOf s ctx Known.fFunction
  let strictSlot := (n.fieldId "Strict").bind fun f => fn.bind fun v => fieldOf s v f
  match strictSlot, fn with
  | some (.bool b), _ => s!"{b} (the active function's [[Strict]])"
  | _, some (.obj _) => "n/a (a built-in function: not ECMAScript code)"
  | _, _ =>
    let som := running.bind fun ctx => fieldOf s ctx Known.fScriptOrModule
    let isModule := match som with
      | some v@(.ref _) => (cellType n s v).endsWith "Module Record"
      | _ => false
    if isModule then "true (module code)"
    else match (frames.findSome? (·.node)).map nodeStamp with
      | some k =>
        if s.strictParses.contains k then "true (eval code of a direct eval in strict mode code)"
        else match s.roots[k]? with
          | some root => if Ecma.Grammar.prologueStrict (Ecma.Prims.Nodes.strictView F) root then "true (a Use Strict Directive)" else "false (no Use Strict Directive)"
          | none => "unknown (the code's parse has no root)"
      | none => "unknown (no frame has a Parse Node)"

def contextVars (n : Names) (s : State F) (frames : List FrameView) : List Var :=
  let ctxs := stackList s
  let last := ctxs.length - 1
  let listed := ctxs.zipIdx.map fun (v, i) =>
    cellVar n s (s!"[{i}]" ++ (if i == last then " running" else "")) v
  let running := ctxs.getLast?
  let field := fun (name : String) (f : FieldId) =>
    match running.bind fun ctx => fieldOf s ctx f with
    | some v => cellVar n s name v
    | none => { name, value := "none" : Var }
  listed ++
  [valVar n "resumed" s.resumed, cellVar n s "suspended" s.suspended,
    match running with
    | some v => cellVar n s "running execution context" v
    | none => { name := "running execution context", value := "none (the stack is empty)" },
    field "active function" Known.fFunction, field "current Realm" Known.fRealm,
    cellVar n s "GetActiveScriptOrModule()" (activeScriptOrModule s),
    { name := "strict", value := if running.isSome then strictness n s running frames else "none" }]

/-- A frame's slots; a cell's kind as its type where the pause has the state. -/
def slotVars (n : Names) (st : Option (State F)) (f : FrameView) : List Var :=
  f.slots.map fun (x, v) => match st with
    | some s => cellVar n s x v
    | none => valVar n x v

/-! JS positions. -/

/-- The node of the step a run enters: its parse, span and nonterminal, and whether the step is a
statement boundary (step 1 of a statement row in the outermost frame on a statement node of that
span). -/
structure StepNode where
  stamp : Nat
  lo : Nat
  hi : Nat
  nt : NtId
  boundary : Bool

/-- A statement node of a source's parse: its span in the source's text and its start's line and
column. -/
structure StmtPos where
  lo : Nat
  hi : Nat
  line : Nat
  column : Nat

/-- The statement nodes under the nodes `todo`, in preorder, after `acc`. -/
partial def stmtWalk (n : Names) (p : Program) : List F.Node → Array StmtPos → Array StmtPos
  | [], acc => acc
  | nd :: todo, acc =>
    let acc := if n.stmtNts.contains (nodeNt nd) then
        let (lo, hi) := (p.spanIn? nd).getD (nodeSpan nd)
        let (line, column) := lineCol p.lineStarts lo
        acc.push { lo, hi, line, column }
      else acc
    stmtWalk n p (nodeKids nd ++ todo) acc

/-- A source's statement table from its root Parse Node: one statement node per start (the
outermost), sorted by start. -/
def stmtTable (n : Names) (p : Program) (root : F.Node) : Array StmtPos :=
  let all := (stmtWalk n p [root] #[]).qsort fun a b => a.lo < b.lo || (a.lo == b.lo && a.hi > b.hi)
  all.foldl (fun acc e => if acc.back?.any (·.lo == e.lo) then acc else acc.push e) #[]

/-- Where a breakpoint on `line` (at `column`, if given) resolves: the table's first statement on
that line (at or after that column), else on the next line that has one. -/
def resolveLine (t : Array StmtPos) (line : Nat) (column : Option Nat) : Option StmtPos :=
  t.find? fun e => e.line > line || (e.line == line && e.column ≥ column.getD 0)

/-- Whether the running execution context's function is a built-in one (it has no [[Strict]]). -/
def runningBuiltin (n : Names) (s : State F) : Bool :=
  match (stackList s).getLast?.bind fun ctx => fieldOf s ctx Known.fFunction with
  | some fn@(.obj _) => match (n.fieldId "Strict").bind (fieldOf s fn ·) with
    | some (.bool _) => false
    | _ => true
  | _ => false

/-- A node's span in its source and its start and end positions. -/
def spanFields (p : Program) (nd : F.Node) : List (String × Json) :=
  let (lo, hi) := (p.spanIn? nd).getD (nodeSpan nd)
  let (l, c) := lineCol p.lineStarts lo
  let (el, ec) := lineCol p.lineStarts hi
  [("line", .nat l), ("column", .nat c), ("endLine", .nat el), ("endColumn", .nat ec), ("lo", .nat lo), ("hi", .nat hi)]

/-- The running built-in's algorithm: the frame inside the innermost BuiltinCallOrConstruct, else the
innermost frame's. -/
def builtinName (frames : List FrameView) : String :=
  let rec go (inner : Option FrameView) : List FrameView → Option String
    | [] => none
    | f :: fs => if f.secId == "sec-builtincallorconstruct" then inner.map (·.name) else go (some f) fs
  (go none frames).getD ((frames.head?.map (·.name)).getD "")

/-- A pause's `js`: the innermost node of a parse of a source's text (its source, position and span),
the innermost statement node of one, the running built-in's algorithm where the innermost frame has no
such node and a built-in function is running (`inBuiltin`), and the execution context stack's length. -/
def jsJson (n : Names) (srcs : Sources) (frames : List FrameView) (st : Option (State F)) : Json :=
  let ctxs : List (String × Json) := match st with
    | some s => [("contexts", .nat (stackList s).length)]
    | none => []
  let ours := fun (f : FrameView) => f.node.bind fun nd => (srcs.ofNode? nd).map (·, nd)
  let pos := match frames.findSome? ours with
    | some (p, nd) => ("source", p.sourceJson) :: spanFields p nd
    | none => []
  let stmt := match frames.findSome? fun f => (ours f).filter fun (_, nd) => n.stmtNts.contains (nodeNt nd) with
    | some (p, nd) => [("statement", Json.mk (spanFields p nd))]
    | none => []
  let builtin := match frames.head?, st with
    | some f, some s => if (ours f).isNone && runningBuiltin n s then [("inBuiltin", Json.str (builtinName frames))] else []
    | _, _ => []
  Json.mk (pos ++ stmt ++ builtin ++ ctxs)

end Debugger
