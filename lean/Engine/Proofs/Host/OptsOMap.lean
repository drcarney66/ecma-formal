module

public import Engine.Host.Opts
public import Engine.Model.OMapLaws

@[expose] public section

/-!
# The Impl host's rebuilt Records

`Engine.Host.rebuild` reads as its argument (`get_rebuild`), without `Impl.Laws`. A Record here is a
well-formed map (`Model.WMap`), so where the prover's lemmas carried `OMap.Keyed` these carry nothing.
-/

namespace Engine.Host

open Ecma Engine.Model

theorem putFrom_foldl (sl : WMap FieldId (Val Impl)) (g : FieldId) :
    ∀ (l : List (FieldId × Nat)) (m : WMap FieldId (Val Impl)),
      (l.foldl (putFrom sl) m).get g = (if g ∈ l.map Prod.fst then sl.get g else none).or (m.get g)
  | [], _ => by simp
  | (k, i) :: l, m => by
    have hs : (putFrom sl m (k, i)).get g = (if k = g then sl.get g else none).or (m.get g) := by
      unfold putFrom
      split
      · rename_i v hv
        show ((m.val.put k v).get g) = _
        rw [m.property.get_put]
        split
        · subst g; rw [if_pos rfl, hv]; rfl
        · rename_i hn; rw [if_neg (Ne.symm hn)]; rfl
      · rename_i hv
        split
        · subst g; rw [hv]; rfl
        · rfl
    have ih2 := putFrom_foldl sl g l (putFrom sl m (k, i))
    simp only [List.foldl_cons, ih2, hs, List.map_cons, List.mem_cons]
    by_cases h2 : k = g
    · subst h2
      cases sl.get k <;> by_cases h1 : k ∈ l.map Prod.fst <;> simp [h1]
    · by_cases h1 : g ∈ l.map Prod.fst <;> simp [h1, h2, Ne.symm h2]

theorem rebuild_eq (sl : WMap FieldId (Val Impl)) :
    rebuild sl = sl.index.toList.foldl (putFrom sl) WMap.empty := rfl

/-- `rebuild sl` reads as `sl`. -/
theorem get_rebuild (sl : WMap FieldId (Val Impl)) (g : FieldId) : (rebuild sl).get g = sl.get g := by
  rw [rebuild_eq, putFrom_foldl sl g]
  have he : WMap.get (WMap.empty : WMap FieldId (Val Impl)) g = none := by simp [WMap.get, WMap.empty, OMap.get, OMap.empty]
  rw [he, Option.or_none]
  split
  · rfl
  · rename_i hn
    show none = sl.val.get g
    unfold OMap.get
    split
    · rename_i i hi
      exact absurd (List.mem_map.mpr ⟨(g, i), Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hi, rfl⟩) hn
    · rfl

/-- Puts into a Record: each key put reads as its value. -/
theorem foldl_put (v : Val Impl) (g : FieldId) :
    ∀ (fs : List FieldId) (m : WMap FieldId (Val Impl)),
      (fs.foldl (fun m f => m.put f v) m).get g = if g ∈ fs then some v else m.get g
  | [], _ => by simp
  | f :: fs, m => by
    have ih2 := foldl_put v g fs (m.put f v)
    have hp : (m.put f v).get g = if g = f then some v else m.get g := m.property.get_put f v g
    simp only [List.foldl_cons, ih2, hp, List.mem_cons]
    by_cases h2 : g = f
    · subst h2; by_cases h1 : g ∈ fs <;> simp [h1]
    · by_cases h1 : g ∈ fs <;> simp [h1, h2]

/-- The Byte Length slots `fs` put into `rebuild sl` read as `v`, the others as in `sl`. -/
theorem recGet_resized (sl : Impl.Rec (Val Impl)) (fs : List FieldId) (v : Val Impl) (g : FieldId) :
    Impl.recGet (fs.foldl (fun sl f => Impl.recSet sl f v) (rebuild sl)) g =
      if g ∈ fs then some v else Impl.recGet sl g := by
  have h := foldl_put v g fs (rebuild sl)
  rw [get_rebuild] at h
  exact h

theorem heapGet_set_ne {α : Type} (h : Impl.Heap α) {p q : Nat} (c : α) (ne : p ≠ q) :
    Impl.heapGet (Impl.heapSet h p c) q = Impl.heapGet h q :=
  Array.getElem?_setIfInBounds_ne ne

theorem heapGet_set_self {α : Type} {h : Impl.Heap α} {p : Nat} {c c' : α} (hp : Impl.heapGet h p = some c) :
    Impl.heapGet (Impl.heapSet h p c') p = some c' :=
  Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp hp).1

end Engine.Host
