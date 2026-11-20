module

public import Engine.Model.Case
public import Engine.Model.Normalize
public import Engine.Model.PropSets

@[expose] public section

/-! # The Unicode helpers' results are code points; property sets' elements are well formed -/

namespace Engine

theorem scfPoint?_le {c d : Nat} (h : scfPoint? c = some d) : d ≤ maxPoint := by
  unfold scfPoint? at h
  split at h
  · simp only [Option.filter_eq_some_iff] at h; simpa using h.2
  · cases h

theorem lowerPoints_le {cs : List Nat} {d : Nat} (h : d ∈ lowerPoints cs) : d ≤ maxPoint := by
  simpa using (List.mem_filter.1 h).2

theorem upperPoints_le {cs : List Nat} {d : Nat} (h : d ∈ upperPoints cs) : d ≤ maxPoint := by
  simpa using (List.mem_filter.1 h).2

theorem normalizePoints_le (f : Ecma.NormForm) (cs : List Nat) :
    ∀ c ∈ normalizePoints f cs, c ≤ 0x10FFFF := by
  intro c h
  simpa [normalizePoints] using (List.mem_filter.mp h).2

namespace PropSets

theorem rangesOk_tail {x : Nat × Nat} {r : List (Nat × Nat)} (h : rangesOk (x :: r) = true) :
    rangesOk r = true := by
  match r, h with
  | [], _ => rfl
  | (c, d) :: r, h => simp only [rangesOk, Bool.and_eq_true] at h; exact h.2

theorem rangesOk_head {a b : Nat} {r : List (Nat × Nat)} (h : rangesOk ((a, b) :: r) = true) :
    a ≤ b ∧ b ≤ 0x10FFFF := by
  induction r generalizing a b with
  | nil => simpa [rangesOk] using h
  | cons y r ih =>
    obtain ⟨c, d⟩ := y
    simp only [rangesOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have := ih h.2
    omega

/-- The first range's upper bound is below every later code point. -/
theorem lt_of_rangesOk {a b : Nat} {r : List (Nat × Nat)} (h : rangesOk ((a, b) :: r) = true) :
    ∀ c ∈ expand r, b < c := by
  induction r generalizing a b with
  | nil => simp [expand]
  | cons y r ih =>
    obtain ⟨c, d⟩ := y
    simp only [rangesOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have hcd := rangesOk_head h.2
    intro x hx
    simp only [expand, List.flatMap_cons, List.mem_append, List.mem_range'] at hx
    rcases hx with ⟨i, _, rfl⟩ | hx
    · omega
    · have := ih h.2 x hx
      omega

theorem expand_lt {rs : List (Nat × Nat)} (h : rangesOk rs = true) :
    (expand rs).Pairwise (· < ·) ∧ ∀ c ∈ expand rs, c ≤ 0x10FFFF := by
  induction rs with
  | nil => simp [expand]
  | cons x r ih =>
    obtain ⟨a, b⟩ := x
    have ⟨hp, hb⟩ := ih (rangesOk_tail h)
    have hlt := lt_of_rangesOk h
    have hab := rangesOk_head h
    have e : expand ((a, b) :: r) = List.range' a (b + 1 - a) ++ expand r := rfl
    rw [e]
    refine ⟨List.pairwise_append.2 ⟨List.pairwise_lt_range', hp, ?_⟩, ?_⟩
    · intro x hx y hy
      simp only [List.mem_range'] at hx
      have := hlt y hy
      omega
    · intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · simp only [List.mem_range'] at hc; omega
      · exact hb c hc

theorem strings_ok {ss : List (List Nat)} (h : stringsOk ss = true) :
    ss.Pairwise (fun s t => key s < key t) ∧ ∀ s ∈ ss, 2 ≤ s.length ∧ ∀ c ∈ s, c ≤ 0x10FFFF := by
  induction ss with
  | nil => simp
  | cons s r ih =>
    simp only [stringsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h2, hc⟩, hk⟩, hr⟩ := h
    have ⟨hp, hall⟩ := ih hr
    refine ⟨List.pairwise_cons.2 ⟨?_, hp⟩, ?_⟩
    · match r, hk, hp with
      | [], _, _ => simp
      | t :: r', hk, hp =>
        intro u hu
        simp only at hk
        rcases List.mem_cons.1 hu with rfl | hu
        · exact of_decide_eq_true hk
        · exact Nat.lt_trans (of_decide_eq_true hk) ((List.pairwise_cons.1 hp).1 u hu)
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact ⟨h2, fun c hc' => by simpa using hc c hc'⟩
      · exact hall t ht

theorem find?_some {α : Type} {n : List Nat} {l : List (String × α)} {a : α} (h : Engine.Model.Unicode.find? n l = some a) :
    ∃ k, (k, a) ∈ l ∧ k.toList.map Char.toNat = n := by
  induction l with
  | nil => simp [Engine.Model.Unicode.find?] at h
  | cons x r ih =>
    obtain ⟨k, b⟩ := x
    simp only [Engine.Model.Unicode.find?] at h
    split at h
    · rename_i e
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨k, by simp, e⟩
    · obtain ⟨k', hm, e⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hm, e⟩

/-- Sequences of two or more code points come only with a property of strings (Table 67). -/
theorem strings_of_propertyValue {p v : List Nat} {rs : List (Nat × Nat)} {ss : List (List Nat)}
    (h : Engine.Model.Unicode.propertyValue? p v = some (rs, ss)) (hs : ss ≠ []) :
    ∃ k ∈ Ecma.Unicode.stringPropertyNames.map Prod.fst, k.toList.map Char.toNat = p := by
  unfold Engine.Model.Unicode.propertyValue? at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h; exact absurd rfl hs
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h; exact absurd rfl hs
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨_, _, _, rfl⟩ := h; exact absurd rfl hs
  · split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.2.symm hs
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.2.symm hs
        · simp at h
    · split at h
      · rename_i s hf
        obtain ⟨k, hm, e⟩ := find?_some hf
        exact ⟨k, List.mem_map.2 ⟨(k, s), hm, rfl⟩, e⟩
      · simp at h

/-- The elements are distinct, non-empty sequences of code points; a sequence of two or more
comes only from `Engine.Model.Unicode.propertyValue?`'s sequences. -/
theorem elements_wf {p v : List Nat} {es : List (List Nat)} (h : elements p v = some es) :
    es.Nodup ∧ (∀ e ∈ es, e ≠ [] ∧ ∀ c ∈ e, c ≤ 0x10FFFF) ∧
      ∃ rs ss, Engine.Model.Unicode.propertyValue? p v = some (rs, ss) ∧ ∀ e ∈ es, e.length ≠ 1 → e ∈ ss.mergeSort fun x y => key x ≤ key y := by
  simp only [elements, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨rs, ss⟩, hpv, h⟩ := h
  split at h
  · rename_i hok
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hok
    have ⟨hp, hb⟩ := expand_lt hok.1
    have ⟨sp, sall⟩ := strings_ok hok.2
    refine ⟨?_, ?_, rs, ss, hpv, ?_⟩
    · refine List.nodup_append.2 ⟨?_, ?_, ?_⟩
      · exact (List.Pairwise.map _ (fun a b (h : a < b) (e : [a] = [b]) => by simp at e; omega) hp)
      · exact sp.imp fun h e => by subst e; exact Nat.lt_irrefl _ h
      · intro x hx y hy e
        subst e
        simp only [List.mem_map] at hx
        obtain ⟨c, _, rfl⟩ := hx
        have := (sall _ hy).1
        simp at this
    · intro e he
      rcases List.mem_append.1 he with he | he
      · simp only [List.mem_map] at he
        obtain ⟨c, hc, rfl⟩ := he
        exact ⟨by simp, fun x hx => by simp at hx; rw [hx]; exact hb c hc⟩
      · have := sall e he
        exact ⟨fun e0 => by simp [e0] at this, this.2⟩
    · intro e he hl
      rcases List.mem_append.1 he with he | he
      · simp only [List.mem_map] at he
        obtain ⟨c, _, rfl⟩ := he
        simp at hl
      · exact he
  · simp at h

end PropSets

end Engine
