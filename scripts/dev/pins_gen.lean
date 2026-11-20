import Lean
open Lean

/-!
Writes `lean/Engine/Proofs/Pins/Gen/Eq.lean` and `lean/Engine/Proofs/Pins/Gen/Quote.lean`: for the types the
roots below reach, a Boolean equality test with its soundness (`Engine.Pins.EqB`), and `Lean.ToExpr`.

    nix develop ~/.local/state/ecma-formal/devshell -c \
      lake env lean --run scripts/dev/pins_gen.lean lean/Engine/Proofs/Pins/Gen

A type with no recursion, whose fields' types have decidable equality, gets `deriving instance DecidableEq`.
Every other type (recursive, mutual, nested, or holding one) gets `T.eqB` by structural recursion, with a helper
for each nested shape (`List T`, `Option T`, `A × T`, `Array T`) inside the `mutual` block, and `T.eqB_sound`.
A field's type that is none of these (a function, a `Float`, a type with parameters) is an error.
-/

/-- The types whose values are pinned. -/
def roots : List Name := [`Ecma.Machine.Ins, `Ecma.Alg, `Ecma.SdoRow, `Ecma.Machine.RowCode]

/-- The modules that declare them. -/
def modules : List Name := [`Ecma.Machine.Code]

/-- A field's type. -/
inductive Ty where
  /-- a type of core Lean with decidable equality and `ToExpr` -/
  | base (n : Name)
  /-- an inductive type of the project -/
  | user (n : Name)
  | list (t : Ty)
  | opt (t : Ty)
  | arr (t : Ty)
  | prod (a b : Ty)
  deriving BEq, Inhabited

def baseTypes : List Name := [`Nat, `String, `Bool, `Char, `Int]

/-- A type with the abbreviations at its head unfolded. -/
partial def norm (env : Environment) (e : Expr) : Expr :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const n ls =>
    match env.find? n with
    | some (.defnInfo d) =>
      if d.hints == .abbrev then norm env ((d.value.instantiateLevelParams d.levelParams ls).beta e.getAppArgs)
      else e
    | _ => e
  | _ => e

partial def toTy (env : Environment) (e : Expr) : Except String Ty := do
  let e := norm env e
  match e.getAppFn, e.getAppArgs with
  | .const ``List _, #[x] => return .list (← toTy env x)
  | .const ``Option _, #[x] => return .opt (← toTy env x)
  | .const ``Array _, #[x] => return .arr (← toTy env x)
  | .const ``Prod _, #[x, y] => return .prod (← toTy env x) (← toTy env y)
  | .const n _, #[] =>
    if baseTypes.contains n then return .base n
    match env.find? n with
    | some (.inductInfo iv) =>
      if iv.numParams != 0 || iv.numIndices != 0 then throw s!"{n}: an inductive type with parameters or indices"
      return .user n
    | _ => throw s!"{n}: not an inductive type"
  | _, _ => throw s!"unsupported type {e}"

/-- A constructor's fields' types. -/
partial def ctorFields (env : Environment) (c : Name) : Except String (List Ty) := do
  let some (.ctorInfo ci) := env.find? c | throw s!"{c}: not a constructor"
  let rec go (e : Expr) : Except String (List Ty) := do
    match e with
    | .forallE _ d b _ =>
      if d.hasLooseBVars then throw s!"{c}: a dependent field"
      match toTy env d with
      | .ok t => return t :: (← go b)
      | .error m => throw s!"{c}: {m}"
    | _ => return []
  go ci.type

partial def Ty.users : Ty → List Name
  | .base _ => []
  | .user n => [n]
  | .list t | .opt t | .arr t => t.users
  | .prod a b => a.users ++ b.users

def Ty.mentions (g : List Name) (t : Ty) : Bool := t.users.any g.contains

/-- A type as Lean source. -/
partial def Ty.src : Ty → String
  | .base n | .user n => toString n
  | .list t => s!"(List {t.src})"
  | .opt t => s!"(Option {t.src})"
  | .arr t => s!"(Array {t.src})"
  | .prod a b => s!"({a.src} × {b.src})"

/-- A type as a part of a name. -/
partial def Ty.mangle : Ty → String
  | .base n | .user n => n.getString!
  | .list t => "L" ++ t.mangle
  | .opt t => "O" ++ t.mangle
  | .arr t => "A" ++ t.mangle
  | .prod a b => "P" ++ a.mangle ++ b.mangle

structure Ctx where
  env : Environment
  /-- the types reached, each with its constructors' fields -/
  types : Std.HashMap Name (List (Name × List Ty))
  /-- the types tested by a generated function -/
  gen : List Name

def ind (env : Environment) (n : Name) : InductiveVal :=
  match env.find? n with
  | some (.inductInfo iv) => iv
  | _ => panic! s!"{n}"

/-- The nested shapes of a group's fields that hold a type of the group, components before the shapes holding
them. -/
partial def shapes (g : List Name) (ts : List Ty) : List Ty := Id.run do
  let rec visit (acc : List Ty) (t : Ty) : List Ty :=
    if !t.mentions g || acc.contains t then acc
    else match t with
      | .base _ | .user _ => acc
      | .list x | .opt x | .arr x => visit acc x ++ [t] |>.eraseDups
      | .prod a b => (visit (visit acc a) b ++ [t]).eraseDups
  let mut acc := []
  for t in ts do acc := visit acc t
  return acc

def aux (g : List Name) (t : Ty) : String := s!"{g.head!}.eqB_{t.mangle}"

/-- The test of two values of a field's type. -/
def cmp (g : List Name) (t : Ty) (a b : String) : String :=
  if !t.mentions g then s!"EqB.eqB {a} {b}"
  else match t with
    | .user n => s!"{n}.eqB {a} {b}"
    | _ => s!"{aux g t} {a} {b}"

/-- The test's soundness at a field's type, from `h`. -/
def snd (g : List Name) (t : Ty) (h : String) : String :=
  if !t.mentions g then s!"EqB.sound _ _ {h}"
  else match t with
    | .user n => s!"{n}.eqB_sound _ _ {h}"
    | _ => s!"{aux g t}_sound _ _ {h}"

def vars (p : String) (n : Nat) : List String := (List.range n).map fun i => s!"{p}{i + 1}"

def conj (cs : List String) : String := if cs.isEmpty then "true" else " && ".intercalate cs

/-- The tests of the fields of two constructor applications, over `a1 …` and `b1 …`. -/
def fieldsCmp (g : List Name) (fs : List Ty) : String :=
  conj ((fs.zip (List.range fs.length)).map fun (t, i) => cmp g t s!"a{i + 1}" s!"b{i + 1}")

/-- From `h`, the fields' tests' conjunction, the two applications' equality: the proof's lines. -/
def fieldsProof (g : List Name) (fs : List Ty) (pad : String) : List String :=
  let n := fs.length
  if n == 0 then [pad ++ "rfl"]
  else
    let hs := vars "h" n
    let pat := hs.tail.foldl (fun acc h => s!"⟨{acc}, {h}⟩") hs.head!
    (if n == 1 then [pad ++ "have h1 := h"]
     else [pad ++ "simp only [Bool.and_eq_true] at h", pad ++ s!"obtain {pat} := h"]) ++
    (fs.zip (List.range n)).map (fun (t, i) => pad ++ s!"have e{i + 1} := {snd g t s!"h{i + 1}"}") ++
    [pad ++ s!"subst {" ".intercalate (vars "e" n)}", pad ++ "rfl"]

def ctorPat (c : Name) (p : String) (n : Nat) : String :=
  " ".intercalate (s!".{c.getString!}" :: vars p n)

/-- A group's tests and their soundness. -/
def emitGroup (cx : Ctx) (g : List Name) : List String := Id.run do
  let ctors (t : Name) := cx.types[t]!
  let shs := shapes g (g.flatMap fun t => (ctors t).flatMap (·.2))
  let mut defs : List (List String) := []
  let mut thms : List (List String) := []
  for t in g do
    let cs := ctors t
    let mut d := [s!"def {t}.eqB : {t} → {t} → Bool"]
    let mut p := [s!"theorem {t}.eqB_sound : ∀ a b : {t}, {t}.eqB a b = true → a = b"]
    -- a definition without recursion unfolds to its whole match: the constructor's arm of it
    let unf := s!"    unfold {t}.eqB at h" :: (if (ind cx.env t).isRec || g.length > 1 then [] else ["    dsimp only at h"])
    for (c, fs) in cs do
      let n := fs.length
      if cs.length == 1 then
        d := d ++ [s!"  | {ctorPat c "a" n}, {ctorPat c "b" n} => {fieldsCmp g fs}"]
        p := p ++ [s!"  | {ctorPat c "a" n}, {ctorPat c "b" n}, h => by"] ++ unf ++
          fieldsProof g fs "    "
      else
        d := d ++ [s!"  | {ctorPat c "a" n}, b => match b with",
          s!"    | {ctorPat c "b" n} => {fieldsCmp g fs}", "    | _ => false"]
        p := p ++ [s!"  | {ctorPat c "a" n}, b, h => by"] ++ unf ++ ["    split at h",
          "    · " ++ ((fieldsProof g fs "      ").head!.drop 6).toString] ++ (fieldsProof g fs "      ").tail ++
          ["    · exact absurd h Bool.false_ne_true"]
    defs := defs ++ [d]
    thms := thms ++ [p]
  for s in shs do
    let f := aux g s
    let ty := s.src
    let sig := s!"def {f} : {ty} → {ty} → Bool"
    let thm := s!"theorem {f}_sound : ∀ a b : {ty}, {f} a b = true → a = b"
    match s with
    | .list x =>
      defs := defs ++ [[sig, "  | [], [] => true", s!"  | a :: as, b :: bs => {cmp g x "a" "b"} && {f} as bs",
        "  | _, _ => false"]]
      thms := thms ++ [[thm, "  | [], [], _ => rfl", "  | _ :: _, _ :: _, h => by",
        s!"    simp only [{f}, Bool.and_eq_true] at h", "    obtain ⟨h1, h2⟩ := h",
        s!"    have e1 := {snd g x "h1"}", s!"    have e2 := {f}_sound _ _ h2", "    subst e1 e2", "    rfl",
        s!"  | [], _ :: _, h | _ :: _, [], h => by simp [{f}] at h"]]
    | .opt x =>
      defs := defs ++ [[sig, "  | none, none => true", s!"  | some a, some b => {cmp g x "a" "b"}",
        "  | _, _ => false"]]
      thms := thms ++ [[thm, "  | none, none, _ => rfl", "  | some _, some _, h => by",
        s!"    simp only [{f}] at h", s!"    have e1 := {snd g x "h"}", "    subst e1", "    rfl",
        s!"  | none, some _, h | some _, none, h => by simp [{f}] at h"]]
    | .arr x =>
      defs := defs ++ [[sig, s!"  | ⟨a⟩, ⟨b⟩ => {cmp g (.list x) "a" "b"}"]]
      thms := thms ++ [[thm, "  | ⟨_⟩, ⟨_⟩, h => by", s!"    simp only [{f}] at h",
        s!"    have e1 := {snd g (.list x) "h"}", "    subst e1", "    rfl"]]
    | .prod x y =>
      defs := defs ++ [[sig, s!"  | (a1, a2), (b1, b2) => {cmp g x "a1" "b1"} && {cmp g y "a2" "b2"}"]]
      thms := thms ++ [[thm, "  | (_, _), (_, _), h => by", s!"    simp only [{f}, Bool.and_eq_true] at h",
        "    obtain ⟨h1, h2⟩ := h", s!"    have e1 := {snd g x "h1"}", s!"    have e2 := {snd g y "h2"}",
        "    subst e1 e2", "    rfl"]]
    | _ => pure ()
  let block (ds : List (List String)) : List String :=
    if ds.length == 1 then ds.head! ++ [""]
    else ["mutual"] ++ (ds.map (· ++ [""])).flatten.dropLast ++ ["end", ""]
  return block defs ++ block thms ++ g.map (fun t => s!"instance : EqB {t} := ⟨{t}.eqB, {t}.eqB_sound⟩") ++ [""]

unsafe def main (args : List String) : IO UInt32 := do
  let [dir] := args | do IO.eprintln "usage: pins_gen.lean <output directory>"; return 1
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (modules.toArray.map fun m => { module := m, importAll := true }) {} (loadExts := true)
  -- the types reached
  let mut types : Std.HashMap Name (List (Name × List Ty)) := {}
  let mut todo := roots
  while !todo.isEmpty do
    let t := todo.head!
    todo := todo.tail!
    if types.contains t then continue
    let mut cs := []
    for c in (ind env t).ctors do
      match ctorFields env c with
      | .ok fs =>
        cs := cs ++ [(c, fs)]
        todo := fs.flatMap (·.users) ++ todo
      | .error m => IO.eprintln m; return 1
    types := types.insert t cs
  let deps (t : Name) : List Name := (types[t]!.flatMap fun (_, fs) => fs.flatMap (·.users)).eraseDups
  -- the types with a generated test: the recursive ones, and those holding one
  let mut gen : List Name := []
  let names := types.keys.mergeSort (fun a b => a.toString ≤ b.toString)
  for t in names do
    let iv := ind env t
    if iv.isRec || iv.all.length > 1 || iv.numNested > 0 then gen := t :: gen
  let mut more := true
  while more do
    more := false
    for t in names do
      if !gen.contains t && (deps t).any gen.contains then
        gen := t :: gen
        more := true
  -- the groups, each after the groups it depends on
  let mut done : List Name := []
  let mut order : List (List Name) := []
  let rec visit (fuel : Nat) (t : Name) (done : List Name) (order : List (List Name)) :
      List Name × List (List Name) := Id.run do
    if done.contains t then return (done, order)
    match fuel with
    | 0 => return (done, order)
    | fuel + 1 =>
      let g := (ind env t).all
      let mut done := g ++ done
      let mut order := order
      for d in (g.flatMap deps).eraseDups do
        (done, order) := visit fuel d done order
      return (done, order ++ [g])
  for t in roots do
    (done, order) := visit 1000 t done order
  let cx : Ctx := { env, types, gen }
  let regen := "Generated by scripts/dev/pins_gen.lean; do not edit. To regenerate:\n\n" ++
    "    nix develop ~/.local/state/ecma-formal/devshell -c \\\n" ++
    "      lake env lean --run scripts/dev/pins_gen.lean lean/Engine/Proofs/Pins/Gen"
  let mut eq : List String := ["module", "", "public import Ecma.Machine.Code", "public import Engine.Proofs.Pins.EqB",
    "", "@[expose] public section", "", "/-!", "# A Boolean equality test of the specification's syntax and code, and its soundness", "",
    regen, "", "`T.eqB a b = true → a = b` (`T.eqB_sound`) for each type `Ecma.Machine.Ins`, `Ecma.Alg`, `Ecma.SdoRow` and",
    "`Ecma.Machine.RowCode` reach: by derived `DecidableEq` where the type has no recursion, else by structural",
    "recursion, a helper for each nested shape.", "-/", "", "open Engine.Pins", ""]
  let mut quote : List String := ["module", "", "public import Ecma.Machine.Code", "public import Lean.ToExpr", "",
    "@[expose] public section", "", "/-!", "# The specification's syntax and code as terms (`Lean.ToExpr`)", "", regen, "-/", ""]
  for g in order do
    quote := quote ++ [s!"deriving instance Lean.ToExpr for {", ".intercalate (g.map toString)}"]
    if g.all gen.contains then eq := eq ++ emitGroup cx g
    else eq := eq ++ g.map (fun t => s!"deriving instance DecidableEq for {t}") ++ [""]
  IO.FS.createDirAll dir
  IO.FS.writeFile (System.FilePath.mk dir / "Eq.lean") ("\n".intercalate eq)
  IO.FS.writeFile (System.FilePath.mk dir / "Quote.lean") ("\n".intercalate quote ++ "\n")
  IO.println s!"{types.size} types, {gen.length} with a generated test, {(types.toList.map (·.2.length)).sum} constructors"
  return 0
