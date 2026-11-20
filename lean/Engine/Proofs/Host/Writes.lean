module

public import Engine.Host.SpecOpts
public import Engine.Proofs.Host.Inputs

@[expose] public section

/-!
# The events of a read

`eachByteIx_spec`: `eachByteIx`'s values, index by index; `mem_writesOn`: an event of `writesOn` is one of
the events and writes the byte.
-/

namespace Engine.SpecHost

open Ecma Engine

/-- `eachByteIx` gives `n` values, the one at index `k` `f`'s at `j₀` + `k` and `idx` + `j₀` + `k`. -/
theorem eachByteIx_spec {M : Model} {α : Type} {f : Nat → M.Math → Option α} {idx : M.Math} :
    ∀ {j₀ n : Nat} {ws : List α}, eachByteIx f idx j₀ n = some ws →
    ws.length = n ∧ ∀ k w, ws[k]? = some w → f (j₀ + k) (M.add idx (M.ofNat (j₀ + k))) = some w
  | _, 0, ws, h => by
    simp only [eachByteIx, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun _ _ h => by simp at h⟩
  | j₀, n + 1, ws, h => by
    simp only [eachByteIx, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨w, hw, ws', hr, rfl⟩ := h
    obtain ⟨hl, hk⟩ := eachByteIx_spec hr
    refine ⟨by simp [hl], fun k x hx => ?_⟩
    cases k with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; simpa using hw
    | succ k =>
      simp only [List.getElem?_cons_succ] at hx
      have e : j₀ + (k + 1) = j₀ + 1 + k := by omega
      rw [e]; exact hk k x hx

/-- An event of `insLatest ep es` is `ep` or one of `es`. -/
theorem mem_insLatest {M : Model} {ep q : Val M × (Nat × Nat)} :
    ∀ {es : List (Val M × (Nat × Nat))}, q ∈ insLatest ep es → q = ep ∨ q ∈ es
  | [], h => by simpa [insLatest] using h
  | e :: es, h => by
    simp only [insLatest] at h
    split at h
    · simpa using h
    · simp only [List.mem_cons] at h ⊢
      rcases h with h | h
      · exact .inr (.inl h)
      · rcases mem_insLatest h with h | h
        · exact .inl h
        · exact .inr (.inr h)

/-- An event of `writesOn` is one of the events, and writes the byte. -/
theorem mem_writesOn {M : Model} {isWrite : State M → Val M → Bool} {s : State M} {block : Val M} {loc : M.Math}
    {es : List (Val M × (Nat × Nat))} {q : Val M × (Nat × Nat)} (h : q ∈ writesOn isWrite s block loc es) :
    q ∈ es ∧ writesByte isWrite s block loc q.1 = true := by
  suffices ∀ (l acc : List (Val M × (Nat × Nat))),
      q ∈ l.foldl (fun acc ep => if writesByte isWrite s block loc ep.1 then insLatest ep acc else acc) acc →
      q ∈ acc ∨ q ∈ l ∧ writesByte isWrite s block loc q.1 = true by
    rcases this es [] h with h | h
    · simp at h
    · exact h
  intro l
  induction l with
  | nil => intro acc h; exact .inl h
  | cons e l ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h | ⟨hl, hw⟩
    · split at h
      · rename_i hw
        rcases mem_insLatest h with rfl | h
        · exact .inr ⟨List.mem_cons_self, hw⟩
        · exact .inl h
      · exact .inl h
    · exact .inr ⟨List.mem_cons_of_mem _ hl, hw⟩

end Engine.SpecHost
