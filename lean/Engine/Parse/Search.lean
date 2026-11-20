module

public import Engine.Parse.Kernel

@[expose] public section

/-!
# An exhaustive memoized search over GL

`ends n ps i` is the set of positions `j` such that nonterminal `n` with parameters `ps` derives
the input from `i` to `j` in the alphabet's grammar (`Ecma.Grammar.Derives`), memoized by
(grammar, nonterminal, parameters, position). Left recursion grows a seed: an entry in progress
reads its current set, and the entry is evaluated again until its set stops growing. An entry
that read another entry in progress is provisional and is evaluated again when next asked. The
negative items (`but not`, `∉ N`) read the alphabet's own decision (`negSpan`, `negAny`). A set
is held as intervals (`Ends`): a lexical list's ends from one position are one interval.

Where B.1.2 orders the grammar's alternatives (`orderedIn`), the committed search
(`Ecma.Grammar.Committed`) derives a node of an ordered nonterminal at `i` by the first alternative
that derives some span from `i` in the search without commitment (`firstAlt`), its children
committed.

`build` then makes the Parse Node of a span the committed search found, top down through the
kernel. A node whose span two alternatives derive, or one of whose items has two starts or both
presences, has a second parse: that is a stop, never a choice.
-/

namespace Engine.Parse.Ends

/-- The one position `j`. -/
def single (j : Nat) : Ends := ⟨#[j, j + 1]⟩

/-- No position. -/
def isEmpty (e : Ends) : Bool := e.iv.isEmpty

/-- The greatest position. -/
def max? (e : Ends) : Option Nat := e.iv.back?.map (· - 1)

/-- The greatest position, or `k` where greater or there is none. -/
def maxFrom (e : Ends) (k : Nat) : Nat :=
  match e.max? with
  | some j => max k j
  | none => k

/-- Each position in ascending order, through `f`. -/
@[inline] protected def forIn {m : Type → Type} {β : Type} [Monad m] (e : Ends) (b : β)
    (f : Nat → β → m (ForInStep β)) : m β := do
  let mut acc := b
  for k in [0:e.iv.size / 2] do
    for j in [e.iv[2 * k]!:e.iv[2 * k + 1]!] do
      match ← f j acc with
      | .done b => return b
      | .yield b => acc := b
  return acc

instance {m : Type → Type} [Monad m] : ForIn m Ends Nat where
  forIn e b f := Ends.forIn e b f

/-- The positions, ascending. -/
def toArray (e : Ends) : Array Nat := Id.run do
  let mut out := #[]
  for j in e do out := out.push j
  return out

/-- `acc`'s intervals with `[lo, hi)` joined, `acc`'s none starting after `lo`. -/
@[inline] def addIv (acc : Array Nat) (lo hi : Nat) : Array Nat :=
  if hi ≤ lo then acc
  else match acc.back? with
    | some h => if lo ≤ h then (if h < hi then acc.set! (acc.size - 1) hi else acc) else (acc.push lo).push hi
    | none => (acc.push lo).push hi

/-- The intervals `raw` (flat, in any order, possibly overlapping) as an end set. -/
def norm (raw : Array Nat) : Ends := Id.run do
  let n := raw.size / 2
  let mut sorted := true
  for k in [1:n] do
    if raw[2 * k]! < raw[2 * k - 2]! then
      sorted := false
      break
  let raw := if sorted then raw
    else (((List.range n).map fun k => (raw[2 * k]!, raw[2 * k + 1]!)).mergeSort fun p q => p.1 ≤ q.1).foldl
      (fun a p => (a.push p.1).push p.2) (Array.mkEmpty raw.size)
  let mut out := Array.mkEmpty raw.size
  for k in [0:n] do
    out := addIv out raw[2 * k]! raw[2 * k + 1]!
  return ⟨out⟩

/-- The positions `xs`, in any order, as an end set. -/
def ofArray (xs : Array Nat) : Ends :=
  norm (xs.foldl (fun a x => (a.push x).push (x + 1)) (Array.mkEmpty (2 * xs.size)))

/-- The intervals `ys` after `acc`'s, joined. -/
def appendIvs (acc ys : Array Nat) : Array Nat := Id.run do
  let mut out := acc
  for k in [0:ys.size / 2] do
    out := addIv out ys[2 * k]! ys[2 * k + 1]!
  return out

/-- The first interval of `e` ending after `x`. -/
def firstAfter (e : Ends) (x : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := e.iv.size / 2
  for _ in [0:e.iv.size / 2 + 1] do
    if lo ≥ hi then break
    let m := (lo + hi) / 2
    if e.iv[2 * m + 1]! ≤ x then lo := m + 1 else hi := m
  return lo

/-- The positions in `a` or `b`. -/
def union (a b : Ends) : Ends := Id.run do
  let (x, y) := (a.iv, b.iv)
  if x.isEmpty then return b
  if y.isEmpty then return a
  if x.back! ≤ y[0]! then return ⟨appendIvs x y⟩
  if y.back! ≤ x[0]! then return ⟨appendIvs y x⟩
  let mut out := Array.mkEmpty (x.size + y.size)
  let mut i := 0
  let mut j := 0
  for _ in [0:(x.size + y.size) / 2] do
    if i < x.size && (y.size ≤ j || x[i]! ≤ y[j]!) then
      out := addIv out x[i]! x[i + 1]!
      i := i + 2
    else
      out := addIv out y[j]! y[j + 1]!
      j := j + 2
  return ⟨out⟩

/-- `x` is in `e`. -/
def mem (e : Ends) (x : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := e.iv.size / 2
  for _ in [0:e.iv.size / 2 + 1] do
    if lo ≥ hi then break
    let m := (lo + hi) / 2
    if x < e.iv[2 * m]! then hi := m
    else if x < e.iv[2 * m + 1]! then return true
    else lo := m + 1
  return false

/-- The positions in `a` not in `b`. -/
def diff (a b : Ends) : Ends := Id.run do
  let y := b.iv
  let mut out := #[]
  let mut j := if a.iv.isEmpty then 0 else 2 * b.firstAfter a.iv[0]!
  for k in [0:a.iv.size / 2] do
    let mut lo := a.iv[2 * k]!
    let hi := a.iv[2 * k + 1]!
    for _ in [0:y.size / 2 + 1] do
      if hi ≤ lo || y.size ≤ j then break
      let (bl, bh) := (y[j]!, y[j + 1]!)
      if bh ≤ lo then j := j + 2
      else if hi ≤ bl then break
      else
        if lo < bl then out := (out.push lo).push bl
        lo := bh
        if bh ≤ hi then j := j + 2 else break
    if lo < hi then out := (out.push lo).push hi
  return ⟨out⟩

/-- The positions of `e` where `p` holds. -/
def filterM {m : Type → Type} [Monad m] (e : Ends) (p : Nat → m Bool) : m Ends := do
  let mut out := #[]
  for j in e do
    if ← p j then out := addIv out j (j + 1)
  return ⟨out⟩

/-- The positions of `e` where `p` holds, purely. -/
def filter (e : Ends) (p : Nat → Bool) : Ends := Id.run (e.filterM fun j => pure (p j))

end Engine.Parse.Ends

namespace Engine.Parse.Search

open Ecma.Grammar

variable {N T : Type} (A : Alpha N T)

def tick : SM T Unit := do
  let s ← get
  if s.steps == 0 then throw .fuel
  set { s with steps := s.steps - 1 }

/-- The memo key of `n` under `ps` at `i`, committed (`c`) where B.1.2 orders the grammar. -/
def key (c : Bool) (n : NT) (ps : List Param) (i : Nat) : Key :=
  (A.g.ctorIdx, n.ctorIdx, paramBits ps, i, c && !(orderedIn A.cx A.g).isEmpty)

/-- The ends of a nonterminal symbol from `h`: its derivations, or one input element as a leaf. -/
def ntEnds (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (h : Nat) :
    SM T Ends := do
  if (ruleIn A.g n.ctorIdx).isSome then rec n ps h
  else return Ends.ofArray (← A.leaf n h).toArray

/-- The ends `js` of the child `n` of `lhs` from `h` that the item after it (`next`) admits. -/
def admit (lhs n : NT) (next : Option Item) (h : Nat) (js : Ends) : SM T Ends :=
  match next with
  | some (.onlyIf c) => js.filterM fun j => return A.keep lhs n j && (← A.cond c h j)
  | _ => pure (if A.keepAll lhs n then js else js.filter (A.keep lhs n))

/-- The positions after item `k` (`it`, followed by `next`) of written alternative `alt` of
`lhs`'s rule, from each of the positions `P`, under `ps`. -/
def stepItem (rec : NT → List Param → Nat → SM T Ends) (lhs : NT) (alt k : Nat) (ps : List Param)
    (it : Item) (next : Option Item) (P : Ends) : SM T Ends := do
  let out ← match it with
    | .sym (.t x) o => do
      let mut P' : Array Nat := #[]
      for h in P do
        if let some j ← A.term lhs alt k x h then P' := P'.push j
      pure (if o then (Ends.ofArray P').union P else Ends.ofArray P')
    | .sym (.nt n args) o => do
      let mut raw : Array Nat := #[]
      for h in P do
        raw := raw ++ (← admit A lhs n next h (← ntEnds A rec n (applyArgs ps args) h)).iv
      pure (if o then (Ends.norm raw).union P else Ends.norm raw)
    | .butNot base ex => do
      let mut P' : Array Nat := #[]
      for h in P do
        let js ← match base with
          | .t x => pure (Ends.ofArray (← A.term lhs alt k x h).toArray)
          | .nt n args => ntEnds A rec n (applyArgs ps args) h
        for j in js do
          unless ← excluded A lhs alt k ps h j ex do P' := P'.push j
      pure (Ends.ofArray P')
    | .phrase p => do
      let mut P' : Array Nat := #[]
      for h in P do
        if let some j ← A.phrase p h then P' := P'.push j
      pure (Ends.ofArray P')
    | .lookahead l => P.filterM (lookOk A l)
    | .noLT => P.filterM A.noLT
    | .empty | .onlyIf _ => pure P
  match it with
  | .sym .. | .butNot .. | .phrase _ => if let some j := out.max? then A.hit j
  | _ => pure ()
  return out

/-- The positions reachable before each item of `is` from item `k0` on, from the positions `P`,
and after the last. -/
def forwardFrom (rec : NT → List Param → Nat → SM T Ends) (lhs : NT) (alt : Nat) (ps : List Param)
    (k0 : Nat) (P : Ends) (is : List Item) : SM T (Array Ends) := do
  let mut out := #[P]
  for k in [k0:is.length] do
    out := out.push (← stepItem A rec lhs alt k ps is[k]! is[k + 1]? out.back!)
  return out

/-- The positions reachable before each item of `is` from `i`, and after the last. -/
def forward (rec : NT → List Param → Nat → SM T Ends) (lhs : NT) (alt : Nat) (ps : List Param) (i : Nat)
    (is : List Item) : SM T (Array Ends) :=
  forwardFrom A rec lhs alt ps 0 (.single i) is

/-- Alternative `e` of `n` under `ps` starts with `n` under `ps`: a direct left recursion. -/
def leftRec (n : NT) (ps : List Param) (e : Eff) : Bool :=
  match e.alt.rhs with
  | .sym (.nt m args) false :: _ => m == n && paramBits (applyArgs ps args) == paramBits ps
  | _ => false

/-- The alternatives of `n` in effect under `ps`. -/
def altsUnder (n : NT) (ps : List Param) : List Eff :=
  ((effAlts A.g A.rd A.cx n.ctorIdx).getD []).filter (·.alt.guard.all (Guard.holds ps))

/-- B.1.2's order: the first alternative of `n` under `ps` that derives some span from `i`, the
derivations read by `rec` (the search without commitment); memoized. -/
def firstAlt (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) :
    SM T (Option Eff) := do
  let k := key A false n ps i
  if let some r := (← get).first[k]? then return r
  let mut r := none
  for e in altsUnder A n ps do
    unless (← forward A rec e.rule.lhs e.idx ps i e.alt.rhs).back!.isEmpty do
      r := some e
      break
  modify fun s => { s with first := s.first.insert k r }
  return r

/-- The alternatives of `n` under `ps` a node at `i` may use: committed (`c`) at a nonterminal B.1.2
orders, the first that derives some span from `i` (`pl`, the search without commitment); else
those in effect. -/
def altsAt (pl : NT → List Param → Nat → SM T Ends) (c : Bool) (n : NT) (ps : List Param) (i : Nat) :
    SM T (List Eff) := do
  if c && (orderedIn A.cx A.g).contains n.ctorIdx then return (← firstAlt A pl n ps i).toList
  else return altsUnder A n ps

/-- The ends of the alternatives `es` from `i`. -/
def ruleEnds (rec : NT → List Param → Nat → SM T Ends) (es : List Eff) (ps : List Param) (i : Nat) :
    SM T Ends := do
  let mut acc : Ends := {}
  for e in es do
    acc := acc.union (← forward A rec e.rule.lhs e.idx ps i e.alt.rhs).back!
  return acc

/-- The ends a direct left recursion `e` of `n` from `i` adds to the ends `P` of its first item. -/
def leftStep (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (e : Eff)
    (P : Ends) : SM T Ends := do
  let P ← admit A e.rule.lhs n e.alt.rhs[1]? i P
  if let some j := P.max? then A.hit j
  return (← forwardFrom A rec e.rule.lhs e.idx ps 1 P e.alt.rhs).back!

/-- The ends a direct left recursion's alternatives `dir` of `n` from `i` add to the ends `P` of their first item. -/
def leftAll (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (dir : List Eff)
    (P : Ends) : SM T Ends := do
  let mut add : Ends := {}
  for e in dir do
    add := add.union (← leftStep A rec n ps i e P)
  return add

/-- Rounds of entry `k`'s direct left recursions `dir` from its ends `cur`, the last round having added
`delta`, within `f` rounds: the ends, and whether a round read an entry in progress (the ends then
those before it). -/
def growLeft (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (dir : List Eff)
    (k : Key) : Nat → Ends → Ends → SM T (Ends × Bool)
  | 0, _, _ => throw (.check "a left recursion without a fixpoint")
  | f + 1, cur, delta => do
    tick
    let add ← leftAll A rec n ps i dir delta
    unless (← get).reads.isEmpty do return (cur, true)
    let delta := add.diff cur
    if delta.isEmpty then return (cur, false)
    let cur := cur.union delta
    modify fun s => { s with memo := s.memo.insert k ⟨cur, false, s.hzn, s.far, s.gen⟩ }
    growLeft rec n ps i dir k f cur delta

/-- Rounds of entry `k` evaluating every alternative `es` from its ends `cur`, within `f` rounds, the
reads before them `outer`: the ends, and whether the last round read another entry in progress. -/
def growAll (rec : NT → List Param → Nat → SM T Ends) (es : List Eff) (ps : List Param) (i : Nat) (k : Key)
    (outer : Std.HashSet Key) : Nat → Ends → SM T (Ends × Bool)
  | 0, _ => throw (.check "a recursion without a fixpoint")
  | f + 1, cur => do
    tick
    modify fun s => { s with reads := {} }
    let es' ← ruleEnds A rec es ps i
    let rs := (← get).reads
    let rd := rs.erase k
    modify fun s => { s with reads := outer.insertMany rd.toList }
    let next := cur.union es'
    if rs.isEmpty then return (next, !rd.isEmpty)
    if next == cur then return (cur, !rd.isEmpty)
    modify fun s => { s with memo := s.memo.insert k ⟨next, false, s.hzn, s.far, s.gen⟩ }
    growAll rec es ps i k outer f next

/-- Entry `k`'s rounds where it has direct left recursions `dir` among its alternatives `es`, the rest
`rest`, from its ends `seed`, within `f` rounds each, the reads before them `outer`: the rest once, then
`growLeft`; every alternative each round (`growAll`) where either reads an entry in progress. -/
def viaLeft (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (es dir rest : List Eff)
    (k : Key) (outer : Std.HashSet Key) (f : Nat) (seed : Ends) : SM T (Ends × Bool) := do
  tick
  modify fun s => { s with reads := {} }
  let base := seed.union (← ruleEnds A rec rest ps i)
  if !(← get).reads.isEmpty then return ← growAll A rec es ps i k outer f seed
  modify fun s => { s with memo := s.memo.insert k ⟨base, false, s.hzn, s.far, s.gen⟩ }
  let (cur, general) ← growLeft A rec n ps i dir k f base base
  if general then return ← growAll A rec es ps i k outer f cur
  modify fun s => { s with reads := outer }
  return (cur, false)

/-- Entry `k` of `n` under `ps` at `i` evaluated from `seed`, the reads and the furthest positions before
it `outer`, `outerH`, `outerF`, its nonterminals read by `rec` (`pl`, the search without commitment):
in progress until its rounds end, then final where the last round read no other entry in progress. -/
def evalEntry (rec pl : NT → List Param → Nat → SM T Ends) (size : Nat) (c : Bool) (n : NT) (ps : List Param)
    (i : Nat) (k : Key) (outer : Std.HashSet Key) (outerH outerF : Nat) (seed : Entry) : SM T Ends := do
  modify fun s => { s with active := s.active.insert k, memo := s.memo.insert k { seed with final := false, gen := s.gen },
                           hzn := seed.hzn, far := seed.far }
  let es ← altsAt A pl c n ps i
  let (dir, rest) := es.partition (leftRec n ps)
  let (cur, others) ← if dir.isEmpty then growAll A rec es ps i k outer (size - i + 2) seed.ends
    else viaLeft A rec n ps i es dir rest k outer (size - i + 2) seed.ends
  modify fun s => { s with active := s.active.erase k, memo := s.memo.insert k ⟨cur, !others, s.hzn, s.far, s.gen⟩,
                           hzn := max outerH s.hzn, far := max outerF s.far }
  return cur

/-- `ends c n ps i`, within recursion depth `d`; `size` bounds the positions; committed (`c`), a
node of a nonterminal B.1.2 orders uses its first alternative deriving some span (`altsAt`). An entry
whose evaluation reads no entry in progress is final after one round. With direct left recursions,
and no other read of an entry in progress, each round steps those from the ends the last round added
(the rest of the alternatives once); otherwise each round evaluates every alternative again. An
entry keeps the furthest position read and reached by its evaluation and the entries it read; an
entry of an earlier generation is read only where it still holds (`St.valid`). -/
def ends (size : Nat) : Bool → Nat → NT → List Param → Nat → SM T Ends
  | _, 0, _, _, _ => throw .depth
  | c, d + 1, n, ps, i => do
    let k := key A c n ps i
    let s ← get
    match s.memo[k]?.filter (s.valid i) with
    | some e =>
      if e.final then
        set { s with hzn := max s.hzn e.hzn, far := max s.far e.far }
        return e.ends
      if s.active.contains k then
        set { s with reads := s.reads.insert k }
        return e.ends
      evalEntry A (fun n ps i => ends size c d n ps i) (fun n ps i => ends size false d n ps i) size c n ps i k s.reads
        s.hzn s.far e
    | none =>
      evalEntry A (fun n ps i => ends size c d n ps i) (fun n ps i => ends size false d n ps i) size c n ps i k s.reads
        s.hzn s.far ⟨{}, false, 0, 0, 0⟩

/-- `ends c`, from final entries only. -/
def finalEndsAt (size : Nat) (c : Bool) (d : Nat) (n : NT) (ps : List Param) (i : Nat) : SM T Ends := do
  let es ← ends A size c d n ps i
  match (← get).memo[key A c n ps i]? with
  | some e => if e.final then pure es else throw (.check "a read of a provisional entry")
  | none => throw (.check "a read without an entry")

/-- The ends a built node's items read, committed, from final entries only. -/
def finalEnds (size d : Nat) (n : NT) (ps : List Param) (i : Nat) : SM T Ends :=
  finalEndsAt A size true d n ps i

/-- The starts in `before` from which the present symbol `x` (item `k`, followed by `next`)
derives up to `cur`, each with how to build its piece. -/
def splits (rd : NT → List Param → Nat → SM T Ends) (child : NT → List Param → Nat → Nat → SM T N)
    (lhs : NT) (alt k : Nat) (ps : List Param) (x : Sym) (next : Option Item) (before : Array Nat) (cur : Nat)
    (ex : Option Exclusion) : SM T (List (Nat × SM T (Piece N))) := do
  let mut out := []
  for h in before do
    if let some e := ex then
      if ← excluded A lhs alt k ps h cur e then continue
    match x with
    | .t t => if (← A.term lhs alt k t h) == some cur then out := out ++ [(h, pure (.span h cur))]
    | .nt m args =>
      let ps' := applyArgs ps args
      let ok ← if (ruleIn A.g m.ctorIdx).isSome then pure ((← rd m ps' h).mem cur)
        else pure ((← A.leaf m h) == some cur)
      let ok := ok && A.keep lhs m cur && (← match next with
        | some (.onlyIf c) => if ok then A.cond c h cur else pure true
        | _ => pure true)
      if ok then
        out := out ++ [(h, do
          if (ruleIn A.g m.ctorIdx).isSome then return .kid (← child m ps' h cur) h cur
          else return .kid (← A.leafNode m h cur) h cur)]
  return out

/-- A forward pass of an alternative to build: the positions before each item and after the
last; for a direct left recursion, by item, the starts from which the item reaches each end. -/
structure Fwd where
  sets : Array Ends
  prov : Option (Array (Std.HashMap Nat (Array Nat)))

/-- The starts item `k` may reach `cur` from: every start before it, or those the pass recorded. -/
def Fwd.cand (f : Fwd) (k cur : Nat) : Array Nat :=
  match f.prov with
  | some p => ((p[k]?).bind (·[cur]?)).getD #[]
  | none => f.sets[k]!.toArray

/-- By item of `is`, the starts in `sets` from which it reaches each end. -/
def provOf (rd : NT → List Param → Nat → SM T Ends) (lhs : NT) (alt : Nat) (ps : List Param)
    (is : List Item) (sets : Array Ends) : SM T (Array (Std.HashMap Nat (Array Nat))) := do
  let mut out := #[]
  for k in [0:is.length] do
    let mut m : Std.HashMap Nat (Array Nat) := {}
    match is[k]! with
    | .sym .. | .butNot .. | .phrase _ =>
      for h in sets[k]! do
        for j in ← stepItem A rd lhs alt k ps is[k]! is[k + 1]? (.single h) do
          m := m.insert j ((m.getD j #[]).push h)
    | _ => pure ()
    out := out.push m
  return out

/-- The forward pass of alternative `e` of `n` under `ps` from `i`; a direct left recursion's once
per search. -/
def fwdOf (rd : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (e : Eff) :
    SM T Fwd := do
  if !leftRec n ps e then return ⟨← forward A rd e.rule.lhs e.idx ps i e.alt.rhs, none⟩
  let c := (key A true n ps i, e.wg.ctorIdx, e.idx, e.fresh)
  if let some (sets, prov) := (← get).fwd[c]? then return ⟨sets, some prov⟩
  let sets ← forward A rd e.rule.lhs e.idx ps i e.alt.rhs
  let prov ← provOf A rd e.rule.lhs e.idx ps e.alt.rhs sets
  modify fun s => { s with fwd := s.fwd.insert c (sets, prov) }
  return ⟨sets, some prov⟩

/-- The alternative of `n` under `ps` a node over `i` to `j` uses, among `es`, with its forward pass
over `rd`: at a nonterminal B.1.2 orders only the first deriving some span from `i` (`pl`, the
search without commitment); a second deriving the span is a stop. -/
def pick (rd pl : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i j : Nat) (es : List Eff) :
    SM T (Option (Eff × Fwd)) := do
  let es ← if (orderedIn A.cx A.g).contains n.ctorIdx then pure (← firstAlt A pl n ps i).toList else pure es
  let mut found : Option (Eff × Fwd) := none
  for e in es do
    unless e.alt.guard.all (Guard.holds ps) do continue
    let fw ← fwdOf A rd n ps i e
    unless fw.sets.back!.mem j do continue
    if found.isSome then throw (.ambiguous s!"{n.name}: two alternatives")
    found := some (e, fw)
  return found

/-- The Parse Node of `n` with parameters `ps` over `i` to `j`, a span the committed search found,
within depth `d`; `D` bounds the searches it asks. -/
def build (B : Builder N) (size D stamp : Nat) : Nat → NT → List Param → Nat → Nat → SM T N
  | 0, _, _, _, _ => throw .depth
  | d + 1, n, ps, i, j => do
    let rd := finalEnds A size D
    let some es := effAlts A.g A.rd A.cx n.ctorIdx | throw (.check "no rule to build")
    let found ← pick A rd (finalEndsAt A size false D) n ps i j es
    let some (e, fw) := found | throw (.check "no alternative derives a found span")
    let (a, idx, r) := (e.alt, e.idx, e.rule)
    let child := fun m ps' h c => build B size D stamp d m ps' h c
    let mut cur := j
    let mut pieces : List (Piece N) := []
    let mut mask : List Bool := []
    for k' in [0:a.rhs.length] do
      let k := a.rhs.length - 1 - k'
      let before := fw.sets[k]!
      let next := a.rhs[k + 1]?
      match a.rhs[k]! with
      | .sym x o =>
        let absent := o && before.mem cur
        let present ← splits A rd child r.lhs idx k ps x next (fw.cand k cur) cur none
        if (if absent then 1 else 0) + present.length > 1 then
          throw (.ambiguous s!"{n.name}: two parses of an item")
        if absent then
          pieces := .absent :: pieces
          mask := false :: mask
        else
          let some (h, mkPiece) := present.head? | throw (.check "no split for a symbol")
          pieces := (← mkPiece) :: pieces
          if o then mask := true :: mask
          cur := h
      | .butNot base ex =>
        let present ← splits A rd child r.lhs idx k ps base none (fw.cand k cur) cur (some ex)
        if present.length > 1 then throw (.ambiguous s!"{n.name}: two parses of an item")
        let some (h, mkPiece) := present.head? | throw (.check "no split for a but-not item")
        pieces := (← mkPiece) :: pieces
        cur := h
      | .phrase p =>
        let mut hs : Array Nat := #[]
        for h in fw.cand k cur do
          if (← A.phrase p h) == some cur then hs := hs.push h
        if hs.size > 1 then throw (.ambiguous s!"{n.name}: two parses of a phrase")
        let some h := hs[0]? | throw (.check "no split for a phrase")
        pieces := .span h cur :: pieces
        cur := h
      | _ =>
        unless before.mem cur do throw (.check "no split for a zero-width item")
        pieces := .zero :: pieces
    unless cur == i do throw (.check "no split at the start")
    let some p := effId A.rd e mask | throw (.check "no production id")
    mk B A stamp p ps i j pieces

end Engine.Parse.Search
