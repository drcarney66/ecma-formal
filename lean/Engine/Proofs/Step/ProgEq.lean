module

public import Engine.Machine
public import Ecma.Implements

@[expose] public section

/-!
# The engine's program is the specification's

`Engine.P` and `Engine.P'` are the specification's program and code table (`Ecma.Spec.program`) with each unit
looked up through a table of thunks (`Prog.memo`, `Prog'.memo`). A table's answer at a key is the function's
value there (`memoGet_eq`; `Memo.get_key`, where the key is one-to-one), so each table is the function it memoizes
(`Prog.memo_eq`, `Prog'.memo_eq`), and the engine's program is the specification's with the host's algorithms
(`Engine.P_eq`, `Engine.P'_eq`).
-/

namespace Engine.Machine

open Ecma Ecma.Machine

/-- A table's answer at the key of `a`, with `f a` as the fallback, is `f a`, where the key is one-to-one: an entry
at that key is `f` at an argument of the same key. -/
theorem Memo.get_key {α κ β : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (key : α → κ)
    (hk : ∀ a a', key a = key a' → a = a') (keys : List α) (f : α → β) (a : α) :
    (Memo.of key keys f).get (key a) (fun _ => f a) = f a := by
  have inv : ∀ (keys : List α) (m : Std.HashMap κ (Thunk β)),
      (∀ (k : κ) (t : Thunk β), m[k]? = some t → ∃ a, key a = k ∧ t.get = f a) →
      ∀ (k : κ) (t : Thunk β), (keys.foldl (fun m a => m.insert (key a) (Thunk.mk fun _ => f a)) m)[k]? = some t →
        ∃ a, key a = k ∧ t.get = f a := by
    intro keys
    induction keys with
    | nil => intro m h; exact h
    | cons a as ih =>
      intro m h
      apply ih
      intro k t ht
      rw [Std.HashMap.getElem?_insert] at ht
      split at ht
      · cases ht
        exact ⟨a, eq_of_beq ‹_›, rfl⟩
      · exact h k t ht
  unfold Memo.get Memo.of
  dsimp only
  split
  · rename_i t ht
    obtain ⟨a', h1, h2⟩ := inv keys {} (by intro k t h; simp at h) _ t ht
    rw [h2, hk _ _ h1]
  · rfl

theorem idKey_inj : ∀ a a' : AlgId, idKey a = idKey a' → a = a' := by
  intro ⟨c, i⟩ ⟨c', i'⟩ h
  simp only [idKey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem id_inj {α : Type} : ∀ a a' : α, id a = id a' → a = a' := fun _ _ h => h

theorem memoMap_inv {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (f : κ → α)
    (ks : List κ) (m : Std.HashMap κ (Thunk α)) (hm : ∀ k t, m[k]? = some t → t.get = f k) :
    ∀ k t, (ks.foldl (fun m k => m.insert k (Thunk.mk fun _ => f k)) m)[k]? = some t → t.get = f k := by
  induction ks generalizing m with
  | nil => exact hm
  | cons x ks ih =>
    apply ih
    intro k t h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i heq
      cases h
      have := eq_of_beq heq
      subst this
      rfl
    · exact hm k t h

/-- A memoized function's value is the function's. -/
theorem memoGet_eq {κ α : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ] (f : κ → α)
    (ks : List κ) (k : κ) : memoGet (memoMap f ks) f k = f k := by
  unfold memoGet memoMap
  split
  · rename_i t h
    exact memoMap_inv f ks {} (by intro k t h; simp at h) k t h
  · rfl

/-- The memoized program is the program. -/
theorem Prog.memo_eq (P : Prog) (as os : List AlgId) (rs : List (SdoId × ProdId)) (ps : List ProdId) (nt : Nat) :
    Prog.memo P as os rs ps nt = P := by
  unfold Prog.memo
  simp only [memoGet_eq]

/-- An early-error row's code through the table of a production's rows is the lowering's. -/
theorem earlyRows_get (P : Prog) (p : ProdId) (i : Nat) :
    ((((P.early p).zipIdx.map fun (x : EarlyRow × Nat) => (Prog'.of P).earlyRow p x.2).toArray)[i]?).join =
      (Prog'.of P).earlyRow p i := by
  simp only [Prog'.of, List.getElem?_toArray, List.getElem?_map, List.getElem?_zipIdx]
  cases h : (P.early p)[i]? <;> simp [h]

/-- The memoized code table is the lowering's. -/
theorem Prog'.memo_eq (P : Prog) (algs owners : List AlgId) (rows : List (SdoId × ProdId)) (prods : List ProdId)
    (n : Nat) : Prog'.memo P algs owners rows prods n = Prog'.of P := by
  unfold Prog'.memo
  dsimp only
  have halg := Memo.get_key idKey idKey_inj algs (Prog'.of P).alg
  have hrow := fun s k => Memo.get_key id id_inj rows (fun (x : SdoId × ProdId) => (Prog'.of P).row x.1 x.2) (s, k)
  have hclo := Memo.get_key idKey idKey_inj owners (ownerClos P)
  have hts := Memo.get_key id id_inj (List.range n) (Prog'.of P).tstep
  have her := Memo.get_key id id_inj prods
    (fun p => ((P.early p).zipIdx.map fun (x : EarlyRow × Nat) => (Prog'.of P).earlyRow p x.2).toArray)
  have heo := Memo.get_key id id_inj prods (fun p => (Prog'.of P).earlyOwn [p])
  have hcov := Memo.get_key id id_inj prods (Prog'.of P).covered
  simp only [id] at hrow hts her heo hcov
  conv => rhs; unfold Prog'.of
  congr 1
  · funext a; exact halg a
  · funext s k; exact hrow s k
  · funext site; rw [hclo]
  · funext t; exact hts t
  · funext p i; rw [her]; exact earlyRows_get P p i
  · funext ps
    split
    · exact heo _
    · rfl
  · funext p; exact hcov p

end Engine.Machine

namespace Engine

open Ecma Ecma.Machine

/-- The engine's program is the specification's with the host's algorithms. -/
theorem P_eq : Engine.P = Spec.src.expanded SpecHost.hostAlgs := by
  unfold Engine.P
  exact Machine.Prog.memo_eq ..

/-- The engine's code table is the specification's program with the host's algorithms. -/
theorem P'_eq : Engine.P' = Spec.program SpecHost.hostAlgs := by
  unfold Engine.P'
  split
  rw [Machine.Prog'.memo_eq, P_eq]
  rfl

end Engine
