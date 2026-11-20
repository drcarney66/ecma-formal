module

@[expose] public section

/-!
# Sorted tables as Arrays, searched by bisection

The Unicode tables of the case mappings and the normalization forms
(`Unicode/Gen/CaseData.lean`, `Unicode/Gen/NormalizationData.lean`) are Lists in
code point order, which their lookups walk from the start
(`Unicode.lookupRuns`, `inRanges`, `lookupMapping`, `combiningClass.walk`,
`primaryComposite.walk`). The same tables as Arrays are searched by bisection:
`bisect` counts the entries whose key
is at most a code point, in log₂ of the table's size rounds (a fold over the rounds,
no recursion of its own), and `lastLE` reads the last of them. On a table sorted
by its key, that entry is the only candidate of each walk, so each Array lookup is
its List lookup (proved outside this repository), the tables' order checked by the kernel. A model refactor of the
lookups, which are no steps of ECMA-262: the same results. The searches are
`macro_inline`: compiled code has them in place, with no constant of their own.
-/

namespace Unicode

/-- Round _i_ (from 0) of a bisection of _d_ rounds of the table _a_ (sorted by
_key_) from _lo_ entries whose key is at most _c_: the window's half is
2^(_d_ − 1 − _i_), and the entry before the window's middle decides. -/
@[macro_inline] def bisectRound {α : Type} (key : α → Nat) (a : Array α) (c d : Nat) (lo i : Nat) : Nat :=
  let half := 2 ^ (d - 1 - i)
  match a[lo + half - 1]? with
  | some r => if key r ≤ c then lo + half else lo
  | none => lo

/-- The number of entries of the table _a_ (sorted by _key_) whose key is at most
_c_, when it is at least _lo_ and less than _lo_ + 2^_d_: _d_ rounds of bisection. -/
@[macro_inline] def bisect {α : Type} (key : α → Nat) (a : Array α) (c d lo : Nat) : Nat :=
  (List.range d).foldl (bisectRound key a c d) lo

/-- The last entry of the table _a_ (sorted by _key_) whose key is at most _c_,
if any (`lastLE_eq`). -/
@[macro_inline] def lastLE {α : Type} (key : α → Nat) (a : Array α) (c : Nat) : Option α :=
  let n := bisect key a c (a.size.log2 + 1) 0
  if n = 0 then none else a[n - 1]?

/-- The value of the key _c_ in the table _a_ whose keys increase, by bisection
(`lookupSortedA_eq_lookup`: `List.lookup`). -/
@[macro_inline] def lookupSortedA {β : Type} (a : Array (Nat × β)) (c : Nat) : Option β :=
  match lastLE Prod.fst a c with
  | some (d, m) => if c = d then some m else none
  | none => none

end Unicode

/-- The value of a Unicode Character Database mapping at _c_, for a table that
lists only the code points the mapping changes: _c_ itself when the table does
not list it (CaseFolding.txt: "All code points not listed in this file map to
themselves"; UnicodeData.txt fields 5 and 12–14: "If this field is null, then
the … is the same as the character itself"). -/
def Option.ucdOrSelf {α : Type} (mapped : Option α) (self : α) : α :=
  mapped.getD self
