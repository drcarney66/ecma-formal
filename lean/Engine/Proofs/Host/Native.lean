module

public import Engine.Host.Strategy

@[expose] public section

/-!
# NativeFunctionSource's answer meets its law

The lemmas both hosts (`Engine.RefHost`, `JSSpec.Host`) prove `HostLaws.nativeFunctionSource` with:
a name `nativeName` admits is ASCII without NUL (`nativeName_ascii`), the name `nativeNameOf` reads is
the code units (`nativeNameOf_units`), and `nativeAnswer` keeps the state and answers `nativeWrap`
of it (`nativeAnswer_ok`).
-/

namespace Ecma

/-- An IdentifierName's code point is ASCII and not NUL. -/
theorem ascii_of_identChar {c : Char} (h : (c.isAlphanum || c == '_' || c == '$') = true) :
    0 < c.toNat ∧ c.toNat < 128 := by
  simp only [Char.isAlphanum, Char.isAlpha, Char.isUpper, Char.isLower, Char.isDigit, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with (((h | h) | h) | h) | h
  all_goals first
    | (subst h; decide)
    | (simp only [UInt32.le_iff_toNat_le] at h; simp at h; omega)

/-- An ASCII IdentifierName's code points are ASCII and not NUL. -/
theorem identLike_ascii : ∀ {cs : List Char}, identLike cs = true → ∀ c ∈ cs, 0 < c.toNat ∧ c.toNat < 128
  | [], h => by simp [identLike] at h
  | c :: cs, h => by
    simp only [identLike, Bool.and_eq_true, List.all_eq_true] at h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ascii_of_identChar (by simp only [Bool.or_eq_true] at h ⊢; rcases h.1 with (h1 | h1) | h1 <;> simp [h1, Char.isAlphanum])
    · exact ascii_of_identChar (h.2 d hd)

/-- A key's code points are ASCII and not NUL. -/
theorem keyLike_ascii {cs : List Char} (h : keyLike cs = true) : ∀ c ∈ cs, 0 < c.toNat ∧ c.toNat < 128 := by
  simp only [keyLike, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨⟨hp, hl⟩, hi⟩
  · exact identLike_ascii h
  intro c hc
  obtain ⟨t, rfl⟩ := List.isPrefixOf_iff_prefix.1 hp
  rcases List.mem_append.1 hc with hc | hc
  · exact (by decide : ∀ c ∈ "[Symbol.".toList, 0 < c.toNat ∧ c.toNat < 128) c hc
  have ht : t ≠ [] := by rintro rfl; simp at hl
  rw [List.getLast?_append, List.getLast?_eq_some_getLast ht] at hl
  simp only [Option.some_or, Option.some.injEq] at hl
  have hd : (("[Symbol.".toList ++ t).drop 8).dropLast = t.dropLast := by simp
  rw [hd] at hi
  rw [← List.dropLast_concat_getLast ht, hl] at hc
  rcases List.mem_append.1 hc with hc | hc
  · exact identLike_ascii hi c hc
  · simp only [List.mem_singleton] at hc; subst hc; decide

/-- A name the law admits is ASCII without NUL. -/
theorem nativeName_ascii {cs : List Char} (h : nativeName cs = true) : ∀ c ∈ cs, 0 < c.toNat ∧ c.toNat < 128 := by
  simp only [nativeName, nameLike, Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at h
  rcases h with rfl | h | ⟨hp, hk⟩
  · simp
  · exact keyLike_ascii h
  intro c hc
  have hs : ∀ p : String, p.toList.length = 4 → (∀ c ∈ p.toList, 0 < c.toNat ∧ c.toNat < 128) →
      p.toList.isPrefixOf cs = true → 0 < c.toNat ∧ c.toNat < 128 := by
    intro p hl ha hp
    obtain ⟨t, rfl⟩ := List.isPrefixOf_iff_prefix.1 hp
    rcases List.mem_append.1 hc with hc | hc
    · exact ha c hc
    · exact keyLike_ascii (by rwa [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
        List.nil_append] at hk) c hc
  rcases hp with hp | hp
  · exact hs "get " rfl (by decide) hp
  · exact hs "set " rfl (by decide) hp

/-- A code point that is not NUL reads back from `Char.ofNat`. -/
theorem toNat_ofNat_of_pos {n : Nat} (h : 0 < (Char.ofNat n).toNat) : (Char.ofNat n).toNat = n := by
  unfold Char.ofNat at h ⊢
  split
  · simp [Char.ofNatAux, Char.toNat]
  · rename_i hn; simp [hn, Char.toNat] at h

/-- The name `nativeNameOf` reads from code units is them, ASCII and not NUL. -/
theorem nativeNameOf_units {us : List Nat} {cs : List Char} (h : nativeNameOf (some us) = some cs) :
    nativeName cs = true ∧ cs.map Char.toNat = us ∧ ∀ c ∈ cs, 0 < c.toNat ∧ c.toNat < 128 := by
  simp only [nativeNameOf] at h
  split at h
  · rename_i hn
    cases h
    have ha := nativeName_ascii hn
    refine ⟨hn, ?_, ha⟩
    rw [List.map_map]
    conv => rhs; rw [← List.map_id us]
    exact List.map_congr_left fun u hu => toNat_ofNat_of_pos (ha _ (List.mem_map_of_mem hu)).1
  · cases h

/-- NativeFunctionSource's answer keeps the state and is `nativeWrap` of the name `nativeNameOf` reads. -/
theorem nativeAnswer_ok {M : Model} {us : Option (List Nat)} {s : State M} {r : Val M} {s' : State M}
    (h : nativeAnswer us s = .ok r s') : s' = s ∧ ∃ cs, nativeNameOf us = some cs ∧ r = .str (M.strLit (nativeWrap cs)) := by
  cases hc : nativeNameOf us with
  | some cs =>
    simp only [nativeAnswer, hc, Run.pure, Res.ok.injEq] at h
    exact ⟨h.2.symm, cs, rfl, h.1.symm⟩
  | none => simp [nativeAnswer, hc, Run.stop] at h

/-- _func_.[[InitialName]] where it is the String `y`. -/
theorem initialNameIn_of {M : Model} {s : State M} {a : M.Addr} {sl ps y} (hh : M.heapGet s.heap a = some (.object sl ps))
    (hy : M.recGet sl Known.fInitialName = some (.str y)) : initialNameIn s (.obj a) = some y := by
  simp [initialNameIn, slotOf, hh, hy]

end Ecma
