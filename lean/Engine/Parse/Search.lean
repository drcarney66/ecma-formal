module

public import Engine.Parse.Kernel

@[expose] public section

/-!
# An exhaustive memoized search over GL

`ends n ps i` is the set of positions `j` such that nonterminal `n` with parameters `ps` derives
the input from `i` to `j` in the alphabet's grammar (`Ecma.Grammar.Derives`), memoized by
(grammar, nonterminal, parameters, position). Left recursion grows a seed: an entry in progress
reads its current set, and the entry is evaluated again until its set stops growing (verified by
a final post-fixpoint check over `ruleEnds`). An entry that read another entry in progress is
provisional and is evaluated again when next asked. A set is held as sorted disjoint half-open
intervals (`Ends`): a lexical list's ends from one position are one interval.

Where B.1.2 orders the grammar's alternatives (`orderedBy`), the committed search
(`Ecma.Grammar.Committed`) derives a node of an ordered nonterminal at `i` by the first alternative
that derives some span from `i` in the search without commitment (`firstAlt`), its children
committed.

`build` then makes the Parse Node of a span the committed search found, top down through the
kernel. A node whose span two alternatives derive, or one of whose items has two starts or both
presences, has a second parse: that is a stop (`ambiguous`), never a choice.
-/

namespace Engine.Parse.Ends

/-- Insert half-open interval `[lo, hi)` into a list of intervals, merging adjacent or overlapping intervals. -/
def consIv (lo hi : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => if lo < hi then [(lo, hi)] else []
  | (a, b) :: rest =>
    if b ≤ a then consIv lo hi rest
    else if hi ≤ lo then (a, b) :: rest
    else if hi < a then (lo, hi) :: (a, b) :: rest
    else if b < lo then (a, b) :: consIv lo hi rest
    else consIv (min lo a) (max hi b) rest

/-- Remove half-open interval `[lo, hi)` from a list of intervals. -/
def diffOne (lo hi : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (a, b) :: rest =>
    if b ≤ a then diffOne lo hi rest
    else if hi ≤ lo || b ≤ lo || hi ≤ a then (a, b) :: diffOne lo hi rest
    else
      let l := if a < lo then [(a, lo)] else []
      let r := if hi < b then [(hi, b)] else []
      l ++ r ++ diffOne lo hi rest

/-- The one position `j`. -/
def single (j : Nat) : Ends := ⟨[(j, j + 1)]⟩

/-- No position. -/
def isEmpty (e : Ends) : Bool := e.ivs.all fun (a, b) => b ≤ a

/-- `x` is in `e`. -/
def mem (e : Ends) (x : Nat) : Bool := e.ivs.any fun (lo, hi) => lo ≤ x && x < hi

/-- The positions of `e`, ascending when `e` is normalized. -/
def toList (e : Ends) : List Nat := e.ivs.flatMap fun (lo, hi) => List.range' lo (hi - lo)

/-- The positions as an `Array`. -/
def toArray (e : Ends) : Array Nat := e.toList.toArray

/-- The greatest position, if any. -/
def max? (e : Ends) : Option Nat :=
  e.ivs.foldl (fun acc (lo, hi) => if lo < hi then some (match acc with | some m => max m (hi - 1) | none => hi - 1) else acc) none

/-- The greatest position, or `k` where greater or there is none. -/
def maxFrom (e : Ends) (k : Nat) : Nat :=
  match e.max? with
  | some j => max k j
  | none => k

/-- Merge two interval lists (linear time when sorted, extensionally exact on all lists). -/
def mergeIvs : List (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (a, b) :: xs, (c, d) :: ys =>
    if b ≤ a then mergeIvs xs ((c, d) :: ys)
    else if d ≤ c then mergeIvs ((a, b) :: xs) ys
    else if b < c then (a, b) :: mergeIvs xs ((c, d) :: ys)
    else if d < a then (c, d) :: mergeIvs ((a, b) :: xs) ys
    else if b ≤ d then mergeIvs xs ((min a c, d) :: ys)
    else mergeIvs ((min a c, b) :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Normalize a list of intervals. -/
def ofIvs (raw : List (Nat × Nat)) : Ends :=
  ⟨raw.foldr (fun (lo, hi) acc => consIv lo hi acc) []⟩

/-- The positions `xs` as an end set. -/
def ofList (xs : List Nat) : Ends :=
  ⟨xs.foldr (fun x acc => consIv x (x + 1) acc) []⟩

/-- The positions `xs` as an end set. -/
def ofArray (xs : Array Nat) : Ends := ofList xs.toList

/-- The positions in `a` or `b`. -/
def union (a b : Ends) : Ends :=
  ⟨mergeIvs a.ivs b.ivs⟩

/-- The positions in `a` not in `b`. -/
def diff (a b : Ends) : Ends :=
  ⟨b.ivs.foldl (fun acc (lo, hi) => diffOne lo hi acc) a.ivs⟩

/-- Structural monadic filter over `List Nat`. -/
def filterListM {m : Type → Type} [Monad m] (p : Nat → m Bool) : List Nat → m (List Nat)
  | [] => pure []
  | x :: xs => do
    let keep ← p x
    let rest ← filterListM p xs
    return if keep then x :: rest else rest

/-- The positions of `e` where `p` holds. -/
def filterM {m : Type → Type} [Monad m] (e : Ends) (p : Nat → m Bool) : m Ends := do
  let kept ← filterListM p e.toList
  return ofList kept

/-- The positions of `e` where `p` holds, purely. -/
def filter (e : Ends) (p : Nat → Bool) : Ends := ofList (e.toList.filter p)

instance {m : Type → Type} [Monad m] : ForIn m Ends Nat where
  forIn e b f := forIn e.toList b f

end Engine.Parse.Ends

namespace Engine.Parse.Search

open Ecma.Grammar

variable {N T : Type} (A : Alpha N T)

def tick : SM T Unit := do
  let s ← get
  if s.steps == 0 then throw .fuel
  set { s with steps := s.steps - 1 }

/-- Collect `some` results from `f` across `xs`. -/
def collectM {α β : Type} (f : α → SM T (Option β)) : List α → SM T (List β)
  | [] => pure []
  | x :: xs => do
    let r ← f x
    let rest ← collectM f xs
    return match r with | some y => y :: rest | none => rest

/-- Union `Ends` produced by `f` across `xs`. -/
def foldUnionM {α : Type} (f : α → SM T Ends) : List α → SM T Ends
  | [] => pure {}
  | x :: xs => do
    let e ← f x
    let rest ← foldUnionM f xs
    return e.union rest

/-- The memo key of `n` under `ps` at `i`, committed (`c`) where B.1.2 orders the grammar. -/
def key (c : Bool) (n : NT) (ps : List Param) (i : Nat) : Key :=
  (A.g.ctorIdx, n.ctorIdx, paramBits ps, i, c && orderedBy A.cx A.g)

/-- The ends of a nonterminal symbol from `h`: its derivations, or one input element as a leaf. -/
def ntEnds (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (h : Nat) :
    SM T Ends := do
  if !(altsOf A.cx A.g n).isEmpty then rec n ps h
  else return Ends.ofList (← A.leaf n h).toList

/-- The ends `js` of the child `n` of `lhs` from `h` that the item after it (`next`) admits. -/
def admit (lhs n : NT) (next : Option Item) (h : Nat) (js : Ends) : SM T Ends :=
  match next with
  | some (.onlyIf c) => js.filterM fun j => return A.keep lhs n j && (← A.cond c h j)
  | _ => pure (if A.keepAll lhs n then js else js.filter (A.keep lhs n))

/-- The positions after item `k` (`it`, followed by `next`) of `s`, from each of the positions `P`,
under `ps`. -/
def stepItem (rec : NT → List Param → Nat → SM T Ends) (s : Src) (k : Nat) (ps : List Param)
    (it : Item) (next : Option Item) (P : Ends) : SM T Ends := do
  let out ← match it with
    | .sym (.t x) o => do
      let P' ← collectM (A.term s k x) P.toList
      pure (if o then (Ends.ofList P').union P else Ends.ofList P')
    | .sym (.nt n args) o => do
      let acc ← foldUnionM (fun h => do
        admit A s.rule.lhs n next h (← ntEnds A rec n (applyArgs ps args) h)) P.toList
      pure (if o then acc.union P else acc)
    | .butNot base ex =>
      foldUnionM (fun h => do
        let js ← match base with
          | .t x => pure (Ends.ofList (← A.term s k x h).toList)
          | .nt n args => admit A s.rule.lhs n none h (← ntEnds A rec n (applyArgs ps args) h)
        js.filterM fun j => return !(← excluded A s k ps h j ex)) P.toList
    | .phrase p => do
      let P' ← collectM (A.phrase p) P.toList
      pure (Ends.ofList P')
    | .lookahead l => P.filterM (lookOk A l)
    | .noLT => P.filterM A.noLT
    | .empty | .onlyIf _ => pure P
  match it with
  | .sym .. | .butNot .. | .phrase _ => if let some j := out.max? then A.hit j
  | _ => pure ()
  return out

/-- Step a list of items from index `k`, returning the prefix set before each item and the final end set. -/
def forwardGo (rec : NT → List Param → Nat → SM T Ends) (s : Src) (ps : List Param) :
    Nat → Ends → List Item → SM T (List Ends × Ends)
  | _, P, [] => pure ([], P)
  | k, P, it :: rest => do
    let P' ← stepItem A rec s k ps it rest.head? P
    let (sets, last) ← forwardGo rec s ps (k + 1) P' rest
    pure (P :: sets, last)

/-- The positions reachable before each item of `is` from `i`, and after the last. -/
def forward (rec : NT → List Param → Nat → SM T Ends) (s : Src) (ps : List Param) (i : Nat)
    (is : List Item) : SM T (List Ends × Ends) :=
  forwardGo A rec s ps 0 (.single i) is

/-- Alternative `e` of `n` under `ps` starts with `n` under `ps`: a direct left recursion. -/
def leftRec (n : NT) (ps : List Param) (e : Src) : Bool :=
  match e.alt.rhs with
  | .sym (.nt m args) false :: _ => m == n && paramBits (applyArgs ps args) == paramBits ps
  | _ => false

/-- The alternatives of `n` in effect under `ps`. -/
def altsUnder (n : NT) (ps : List Param) : List Src :=
  (altsOf A.cx A.g n).filter (·.alt.guard.all (Guard.holds ps))

/-- Find the first alternative in `es` deriving a non-empty span from `i` under `rec`. -/
def firstAltLoop (rec : NT → List Param → Nat → SM T Ends) (ps : List Param) (i : Nat) :
    List Src → SM T (Option Src)
  | [] => pure none
  | e :: es => do
    let (_, last) ← forward A rec e ps i e.alt.rhs
    if !last.isEmpty then pure (some e) else firstAltLoop rec ps i es

/-- B.1.2's order: the first alternative of `n` under `ps` that derives some span from `i`, the
derivations read by `rec` (the search without commitment); memoized. -/
def firstAlt (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) :
    SM T (Option Src) := do
  let k := key A false n ps i
  if let some r := (← get).first[k]? then return r
  let r ← firstAltLoop A rec ps i (altsUnder A n ps)
  modify fun s => { s with first := s.first.insert k r }
  return r

/-- The alternatives of `n` under `ps` a node at `i` may use: committed (`c`) at a nonterminal B.1.2
orders, the first that derives some span from `i` (`pl`, the search without commitment); else
those in effect. -/
def altsAt (pl : NT → List Param → Nat → SM T Ends) (c : Bool) (n : NT) (ps : List Param) (i : Nat) :
    SM T (List Src) := do
  if c && (orderedNtsBy A.cx A.g).contains n then return (← firstAlt A pl n ps i).toList
  else return altsUnder A n ps

/-- The ends of the alternatives `es` from `i`. -/
def ruleEnds (rec : NT → List Param → Nat → SM T Ends) (es : List Src) (ps : List Param) (i : Nat) :
    SM T Ends :=
  foldUnionM (fun e => Prod.snd <$> forward A rec e ps i e.alt.rhs) es

/-- The ends a direct left recursion `e` of `n` from `i` adds to the ends `P` of its first item. -/
def leftStep (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (e : Src)
    (P : Ends) : SM T Ends := do
  let tail := e.alt.rhs.drop 1
  let P ← admit A e.rule.lhs n tail.head? i P
  if let some j := P.max? then A.hit j
  return (← forwardGo A rec e ps 1 P tail).2

/-- The ends a direct left recursion's alternatives `dir` of `n` from `i` add to the ends `P` of their first item. -/
def leftAll (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (dir : List Src)
    (P : Ends) : SM T Ends :=
  foldUnionM (leftStep A rec n ps i · P) dir

/-- Rounds of entry `k`'s direct left recursions `dir` from its ends `cur`, the last round having added
`delta`, within `f` rounds: the ends, and whether a round read an entry in progress. -/
def growLeft (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (dir : List Src)
    (k : Key) : Nat → Ends → Ends → SM T (Ends × Bool)
  | 0, _, _ => throw (.check "a left recursion without a fixpoint")
  | f + 1, cur, delta => do
    tick
    let add ← leftAll A rec n ps i dir delta
    unless (← get).reads.isEmpty do return (cur, true)
    let delta := add.diff cur
    if delta.isEmpty then return (cur, false)
    let cur := cur.union delta
    modify fun s => { s with memo := s.memo.insert k ⟨cur, false, s.far⟩ }
    growLeft rec n ps i dir k f cur delta

/-- Rounds of entry `k` evaluating every alternative `es` from its ends `cur`, within `f` rounds, the
reads before them `outer`: the ends, and whether the last round read another entry in progress. -/
def growAll (rec : NT → List Param → Nat → SM T Ends) (es : List Src) (ps : List Param) (i : Nat) (k : Key)
    (outer : Std.HashSet Key) : Nat → Ends → SM T (Ends × Bool)
  | 0, _ => throw (.check "a recursion without a fixpoint")
  | f + 1, cur => do
    tick
    modify fun s => { s with memo := s.memo.insert k ⟨cur, false, s.far⟩, reads := {} }
    let es' ← ruleEnds A rec es ps i
    let rs := (← get).reads
    let rd := rs.erase k
    modify fun s => { s with reads := outer.insertMany rd.toList }
    let next := cur.union es'
    if rs.isEmpty then return (next, false)
    if (es'.diff cur).isEmpty then return (cur, !rd.isEmpty)
    modify fun s => { s with memo := s.memo.insert k ⟨next, false, s.far⟩ }
    growAll rec es ps i k outer f next

/-- Entry `k`'s rounds where it has direct left recursions `dir` among its alternatives `es`, the rest
`rest`, from its ends `seed`, within `f` rounds each, the reads before them `outer`: `rest` once, then
`growLeft`, then a 1-pass `ruleEnds` post-fixpoint check; falls back to `growAll` where an entry in
progress is read besides `k`. -/
def viaLeft (rec : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (es dir rest : List Src)
    (k : Key) (outer : Std.HashSet Key) (f : Nat) (seed : Ends) : SM T (Ends × Bool) := do
  tick
  modify fun s => { s with reads := {} }
  let base := seed.union (← ruleEnds A rec rest ps i)
  if !(← get).reads.isEmpty then return ← growAll A rec es ps i k outer f seed
  modify fun s => { s with memo := s.memo.insert k ⟨base, false, s.far⟩ }
  let (cur, general) ← growLeft A rec n ps i dir k f base base
  if general then return ← growAll A rec es ps i k outer f cur
  modify fun s => { s with memo := s.memo.insert k ⟨cur, false, s.far⟩, reads := {} }
  let chk ← ruleEnds A rec es ps i
  let rd := (← get).reads.erase k
  if !rd.isEmpty || !(chk.diff cur).isEmpty then
    return ← growAll A rec es ps i k outer f (cur.union chk)
  modify fun s => { s with reads := outer }
  return (cur, false)

/-- Entry `k` of `n` under `ps` at `i` evaluated from `seed`, the reads and the furthest position before
it `outer`, `outerF`, its nonterminals read by `rec` (`pl`, the search without commitment):
in progress until its rounds end, then final where the last round read no other entry in progress. -/
def evalEntry (rec pl : NT → List Param → Nat → SM T Ends) (size : Nat) (c : Bool) (n : NT) (ps : List Param)
    (i : Nat) (k : Key) (outer : Std.HashSet Key) (outerF : Nat) (seed : Entry) : SM T Ends := do
  modify fun s => { s with active := s.active.insert k, memo := s.memo.insert k { seed with final := false },
                           far := seed.far }
  let es ← altsAt A pl c n ps i
  let (dir, rest) := es.partition (leftRec n ps)
  let (cur, others) ← if dir.isEmpty then growAll A rec es ps i k outer (size - i + 2) seed.ends
    else viaLeft A rec n ps i es dir rest k outer (size - i + 2) seed.ends
  modify fun s => { s with active := s.active.erase k, memo := s.memo.insert k ⟨cur, !others, s.far⟩,
                           far := max outerF s.far }
  return cur

/-- `ends c n ps i`, within recursion depth `d`; `size` bounds the positions; committed (`c`), a
node of a nonterminal B.1.2 orders uses its first alternative deriving some span (`altsAt`). -/
def ends (size : Nat) : Bool → Nat → NT → List Param → Nat → SM T Ends
  | _, 0, _, _, _ => throw .depth
  | c, d + 1, n, ps, i => do
    let k := key A c n ps i
    let s ← get
    match s.memo[k]? with
    | some e =>
      if e.final then
        set { s with far := max s.far e.far }
        return e.ends
      if s.active.contains k then
        set { s with reads := s.reads.insert k }
        return e.ends
      evalEntry A (fun n ps i => ends size c d n ps i) (fun n ps i => ends size false d n ps i) size c n ps i k s.reads
        s.far e
    | none =>
      evalEntry A (fun n ps i => ends size c d n ps i) (fun n ps i => ends size false d n ps i) size c n ps i k s.reads
        s.far ⟨{}, false, 0⟩

/-- `ends c`, from final entries only. -/
def finalEndsAt (size : Nat) (c : Bool) (d : Nat) (n : NT) (ps : List Param) (i : Nat) : SM T Ends := do
  let es ← ends A size c d n ps i
  match (← get).memo[key A c n ps i]? with
  | some e => if e.final then pure es else throw (.check "a read of a provisional entry")
  | none => throw (.check "a read without an entry")

/-- The ends a built node's items read, committed, from final entries only. -/
def finalEnds (size d : Nat) (n : NT) (ps : List Param) (i : Nat) : SM T Ends :=
  finalEndsAt A size true d n ps i

/-- The starts in `cands` from which the present symbol `x` (item `k`, followed by `next`)
derives up to `cur`, each with how to build its piece. -/
def splits (rd : NT → List Param → Nat → SM T Ends) (child : NT → List Param → Nat → Nat → SM T N)
    (s : Src) (k : Nat) (ps : List Param) (x : Sym) (next : Option Item)
    (cur : Nat) (ex : Option Exclusion) : List Nat → SM T (List (Nat × SM T (Piece N)))
  | [] => pure []
  | h :: hs => do
    let skip ← match ex with
      | some e => excluded A s k ps h cur e
      | none => pure false
    if skip then splits rd child s k ps x next cur ex hs
    else
      let hit? : Option (SM T (Piece N)) ← match x with
        | .t t =>
          if (← A.term s k t h) == some cur then pure (some (pure (.span h cur)))
          else pure none
        | .nt m args => do
          let ps' := applyArgs ps args
          let isRule := !(altsOf A.cx A.g m).isEmpty
          let ok ← if isRule then pure ((← rd m ps' h).mem cur)
            else pure ((← A.leaf m h) == some cur)
          let ok := ok && A.keep s.rule.lhs m cur && (← match next with
            | some (.onlyIf c) => if ok then A.cond c h cur else pure true
            | _ => pure true)
          if ok then
            pure (some (if isRule then return .kid (← child m ps' h cur) h cur
                        else return .kid (← A.leafNode m h cur) h cur))
          else pure none
      let rest ← splits rd child s k ps x next cur ex hs
      return match hit? with
        | some mkPiece => (h, mkPiece) :: rest
        | none => rest

/-- A forward pass of an alternative to build: the positions before each item, after the last,
and (for a direct left recursion) by item, the starts from which the item reaches each end. -/
structure Fwd where
  sets : List Ends
  last : Ends
  prov : Option (List (Std.HashMap Nat (List Nat)))

/-- Record starts in `hs` reaching each end of `it` at index `k`. -/
def provItem (rd : NT → List Param → Nat → SM T Ends) (s : Src) (k : Nat) (ps : List Param)
    (it : Item) (next : Option Item) : List Nat → Std.HashMap Nat (List Nat) → SM T (Std.HashMap Nat (List Nat))
  | [], m => pure m
  | h :: hs, m => do
    let js ← stepItem A rd s k ps it next (.single h)
    let m' := js.toList.foldl (fun acc j => acc.insert j (acc.getD j [] ++ [h])) m
    provItem rd s k ps it next hs m'

/-- By item of `is`, the starts in `sets` from which it reaches each end. -/
def provGo (rd : NT → List Param → Nat → SM T Ends) (s : Src) (ps : List Param) :
    Nat → List Item → List Ends → SM T (List (Std.HashMap Nat (List Nat)))
  | _, [], _ => pure []
  | _, _ :: _, [] => pure []
  | k, it :: rest, before :: restSets => do
    let m ← match it with
      | .sym .. | .butNot .. | .phrase _ => provItem A rd s k ps it rest.head? before.toList {}
      | _ => pure {}
    let ms ← provGo rd s ps (k + 1) rest restSets
    return m :: ms

/-- The forward pass of alternative `e` of `n` under `ps` from `i`; a direct left recursion's once
per search. -/
def fwdOf (rd : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i : Nat) (e : Src) :
    SM T Fwd := do
  if !leftRec n ps e then
    let (sets, last) ← forward A rd e ps i e.alt.rhs
    return ⟨sets, last, none⟩
  let c := (key A true n ps i, e.grammar.ctorIdx, e.idx)
  if let some (e', sets, last, prov) := (← get).fwd[c]? then
    if e' = e then return ⟨sets, last, some prov⟩
  let (sets, last) ← forward A rd e ps i e.alt.rhs
  let prov ← provGo A rd e ps 0 e.alt.rhs sets
  modify fun s => { s with fwd := s.fwd.insert c (e, sets, last, prov) }
  return ⟨sets, last, some prov⟩

/-- Pick the unique matching alternative in `es` deriving `i` to `j`. -/
def pickLoop (rd : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i j : Nat) :
    List Src → Option (Src × Fwd) → SM T (Option (Src × Fwd))
  | [], found => pure found
  | e :: es, found => do
    if !e.alt.guard.all (Guard.holds ps) then
      pickLoop rd n ps i j es found
    else
      let fw ← fwdOf A rd n ps i e
      if !fw.last.mem j then
        pickLoop rd n ps i j es found
      else
        if found.isSome then throw (.ambiguous s!"{n.name}: two alternatives")
        pickLoop rd n ps i j es (some (e, fw))

/-- The alternative of `n` under `ps` a node over `i` to `j` uses, among `es`, with its forward pass
over `rd`: at a nonterminal B.1.2 orders only the first deriving some span from `i` (`pl`, the
search without commitment); a second deriving the span is a stop. -/
def pick (rd pl : NT → List Param → Nat → SM T Ends) (n : NT) (ps : List Param) (i j : Nat) (es : List Src) :
    SM T (Option (Src × Fwd)) := do
  let es ← if (orderedNtsBy A.cx A.g).contains n then pure (← firstAlt A pl n ps i).toList else pure es
  pickLoop A rd n ps i j es none

/-- Candidate starts in `before` for phrase `p` ending at `cur`. -/
def phraseSplits (p : Phrase) (cur : Nat) : List Nat → SM T (List Nat)
  | [] => pure []
  | h :: hs => do
    let hit := (← A.phrase p h) == some cur
    let rest ← phraseSplits p cur hs
    return if hit then h :: rest else rest

/-- Build pieces and optional-presence mask right-to-left across `is` ending at `j`. -/
def buildRhs (rd : NT → List Param → Nat → SM T Ends) (child : NT → List Param → Nat → Nat → SM T N)
    (n : NT) (e : Src) (ps : List Param) (j : Nat) :
    Nat → List Item → List Ends → Option (List (Std.HashMap Nat (List Nat))) →
      SM T (Nat × List (Piece N) × List Bool)
  | _, [], _, _ => pure (j, [], [])
  | _, _ :: _, [], _ => throw (.check "missing forward set")
  | k, it :: rest, before :: restSets, provs => do
    let restProvs ← match provs with
      | none => pure none
      | some (_ :: ps') => pure (some ps')
      | some [] => throw (.check "missing provenance set")
    let (cur, pieces, mask) ← buildRhs rd child n e ps j (k + 1) rest restSets restProvs
    let cands : List Nat := match provs with
      | some (pm :: _) => pm.getD cur []
      | _ => before.toList
    let next := rest.head?
    match it with
    | .sym x o =>
      let absent := o && before.mem cur
      let present ← splits A rd child e k ps x next cur none cands
      if (if absent then 1 else 0) + present.length > 1 then
        throw (.ambiguous s!"{n.name}: two parses of an item")
      if absent then
        return (cur, .absent :: pieces, false :: mask)
      else
        let some (h, mkPiece) := present.head? | throw (.check "no split for a symbol")
        let pc ← mkPiece
        return (h, pc :: pieces, if o then true :: mask else mask)
    | .butNot base ex =>
      let present ← splits A rd child e k ps base none cur (some ex) cands
      if present.length > 1 then throw (.ambiguous s!"{n.name}: two parses of an item")
      let some (h, mkPiece) := present.head? | throw (.check "no split for a but-not item")
      let pc ← mkPiece
      return (h, pc :: pieces, mask)
    | .phrase p =>
      let hs ← phraseSplits A p cur cands
      if hs.length > 1 then throw (.ambiguous s!"{n.name}: two parses of a phrase")
      let some h := hs.head? | throw (.check "no split for a phrase")
      return (h, .span h cur :: pieces, mask)
    | _ =>
      unless before.mem cur do throw (.check "no split for a zero-width item")
      return (cur, .zero :: pieces, mask)

/-- One depth step of `build`, recurring on children via `child`. -/
def buildStep (B : Builder N) (size D stamp : Nat)
    (child : NT → List Param → Nat → Nat → SM T N)
    (n : NT) (ps : List Param) (i j : Nat) : SM T N :=
  let rd := finalEnds A size D
  let es := altsOf A.cx A.g n
  if es.isEmpty then throw (.check "no rule to build")
  else
    pick A rd (finalEndsAt A size false D) n ps i j es >>= fun
      | none => throw (.check "no alternative derives a found span")
      | some (e, fw) =>
        buildRhs A rd child n e ps j 0 e.alt.rhs fw.sets fw.prov >>= fun (cur, pieces, mask) =>
        if cur == i then
          match prodIdOf e mask with
          | none => throw (.check "no production id")
          | some p => mk B A stamp p ps i j pieces
        else throw (.check "no split at the start")

/-- The Parse Node of `n` with parameters `ps` over `i` to `j`, a span the committed search found,
within depth `d`; `D` bounds the searches it asks. -/
def build (B : Builder N) (size D stamp : Nat) : Nat → NT → List Param → Nat → Nat → SM T N
  | 0 => fun _ _ _ _ => throw .depth
  | d + 1 => buildStep A B size D stamp (build B size D stamp d)

end Engine.Parse.Search
