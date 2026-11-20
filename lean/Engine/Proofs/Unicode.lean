module

public import Engine.Proofs.UnicodeLemmas
public import Engine.Proofs.Seq

@[expose] public section

/-!
# The laws of the Unicode operations at the engine's model

The case operations, normalization and the property sets answer code points (`UnicodeLemmas`), each as its integer.
-/

namespace Engine.Impl
open Ecma Engine.Model

/-- A natural number up to 0x10FFFF is a code point. -/
theorem nat_isPoint (c : Nat) (h : c ≤ 0x10FFFF) : Model.isPoint Impl (MathVal.int c) := by
  refine ⟨rfl, ?_, ?_⟩
  · show MathVal.lt (.int c) (.int (0 : Nat)) = false
    rw [MathVal.lt_nat]; exact decide_eq_false (by omega)
  · show MathVal.lt (.int (0x10FFFF : Nat)) (.int c) = false
    rw [MathVal.lt_nat]; exact decide_eq_false (by omega)

/-- A List whose elements are code points' integers is of code points. -/
theorem allPoints_of (xs : Array MathVal) (h : ∀ x ∈ xs.toList, ∃ c : Nat, c ≤ 0x10FFFF ∧ x = MathVal.int c) :
    Model.allPoints Impl xs := by
  intro i x hx
  obtain ⟨k, _, _, hk⟩ := seqGet_idx hx
  obtain ⟨c, hc, rfl⟩ := h x (by rw [← Array.getElem?_toList] at hk; exact List.mem_of_getElem? hk)
  exact nat_isPoint c hc

theorem points_isPoint (cs : List Nat) (hc : ∀ c ∈ cs, c ≤ 0x10FFFF) :
    Model.allPoints Impl (cs.toArray.map fun (c : Nat) => MathVal.int c) := by
  apply allPoints_of
  intro x hx
  simp only [Array.toList_map, List.mem_map] at hx
  obtain ⟨c, hm, rfl⟩ := hx
  exact ⟨c, hc c (by simpa using hm), rfl⟩

/-- The index a property's code point names. -/
def natOf : MathVal → Option Nat := fun
  | .int i => if 0 ≤ i then some i.toNat else none
  | _ => none

theorem natOf_some {x : MathVal} {n : Nat} (h : natOf x = some n) : x = .int n := MathVal.idx_some h

theorem mapM_natOf {xs : List MathVal} {ns : List Nat} (h : xs.mapM natOf = some ns) :
    xs = ns.map fun (n : Nat) => MathVal.int n := by
  induction xs generalizing ns with
  | nil => simp at h; subst h; rfl
  | cons x r ih =>
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨n, hn, ns', hr, rfl⟩ := h
    simp [natOf_some hn, ih hr]

/-- `propSet`'s elements are `PropSets.elements`', as integers. -/
theorem propSet_some {p v : Array MathVal} {es : Array (Array MathVal)} (h : Impl.propSet p v = some es) :
    ∃ pn vn es0, p.toList = pn.map (fun (n : Nat) => MathVal.int n) ∧ PropSets.elements pn vn = some es0 ∧
      es = (es0.map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray := by
  have h : (do
      let es ← PropSets.elements (← p.toList.mapM natOf) (← v.toList.mapM natOf)
      return (es.map fun e => (e.map fun (n : Nat) => MathVal.int n).toArray).toArray) = some es := h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨pn, hp, vn, _, es0, he, rfl⟩ := h
  exact ⟨pn, vn, es0, mapM_natOf hp, he, rfl⟩

/-- The code points of a name. -/
theorem codePointsOf_eq (s : String) :
    (Model.codePointsOf Impl s : Array MathVal).toList = s.toList.map fun c => MathVal.int (c.toNat : Nat) := by
  simp only [Model.codePointsOf]
  induction s.toList with
  | nil => rfl
  | cons c r ih => simp [ih]

theorem int_map_inj {x y : List Nat} (h : x.map (fun (n : Nat) => MathVal.int n) = y.map fun (n : Nat) => MathVal.int n) :
    x = y := by
  have := congrArg (List.map fun (q : MathVal) => (MathVal.bigOf q).toNat) h
  simpa [List.map_map, Function.comp_def, MathVal.bigOf] using this

/-- The engine's model satisfies the Unicode laws. -/
theorem unicodeLaws : Model.UnicodeLaws Impl where
  scf_point c d _ h := by
    change ((MathVal.idx c).bind fun n => (Engine.scfPoint? n).map fun (d : Nat) => MathVal.int d) = some d at h
    cases hi : MathVal.idx c with
    | none => simp [hi] at h
    | some n =>
      simp only [hi, Option.bind_some] at h
      cases he : Engine.scfPoint? n with
      | none => simp [he] at h
      | some e =>
        simp only [he] at h
        cases h
        exact nat_isPoint e (Engine.scfPoint?_le he)
  toLower_points xs _ := points_isPoint _ fun _ h => Engine.lowerPoints_le h
  toUpper_points xs _ := points_isPoint _ fun _ h => Engine.upperPoints_le h
  propSet_chars p v es i e h hi := by
    obtain ⟨pn, vn, es0, _, he, rfl⟩ := propSet_some h
    have ⟨_, hall, _⟩ := PropSets.elements_wf he
    obtain ⟨k, _, _, hk⟩ := seqGet_idx hi
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨e0, he0, rfl⟩ := hk
    have := points_isPoint e0 (hall e0 (List.mem_of_getElem? he0)).2
    simpa using this
  propSet_distinct p v es i j e f h hi hj hij := by
    obtain ⟨pn, vn, es0, _, he, rfl⟩ := propSet_some h
    have ⟨hnd, _, _⟩ := PropSets.elements_wf he
    obtain ⟨a, rfl, _, ha⟩ := seqGet_idx hi
    obtain ⟨b, rfl, _, hb⟩ := seqGet_idx hj
    have hab : a ≠ b := fun e => by
      subst e
      have : MathVal.eq (.int a) (.int a) = false := hij
      rw [(MathVal.eq_iff _ _).2 rfl] at this
      cases this
    refine Classical.byContradiction fun hn => ?_
    have hef : e = f := seq_ext e f fun k => Classical.byContradiction fun hk => hn ⟨k, hk⟩
    subst hef
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ha hb
    obtain ⟨ea, hea, e1⟩ := ha
    obtain ⟨eb, heb, e2⟩ := hb
    have : ea = eb := int_map_inj (by
      have := congrArg Array.toList (e1.trans e2.symm)
      simpa using this)
    subst this
    obtain ⟨la, hia⟩ := List.getElem?_eq_some_iff.1 hea
    obtain ⟨lb, hib⟩ := List.getElem?_eq_some_iff.1 heb
    rcases Nat.lt_or_gt_of_ne hab with h1 | h1
    · exact (List.pairwise_iff_getElem.1 hnd a b la lb h1) (hia.trans hib.symm)
    · exact (List.pairwise_iff_getElem.1 hnd b a lb la h1) (hib.trans hia.symm)
  propSet_strings p v es i e h hi hl := by
    obtain ⟨pn, vn, es0, hp, he, rfl⟩ := propSet_some h
    have ⟨_, _, rs, ss, hpv, hlong⟩ := PropSets.elements_wf he
    obtain ⟨k, _, _, hk⟩ := seqGet_idx hi
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hk
    obtain ⟨e0, he0, rfl⟩ := hk
    have hl0 : e0.length ≠ 1 := fun e1 => by
      have : MathVal.eq (.int ((e0.map fun (n : Nat) => MathVal.int n).toArray.size : Nat)) (.int (1 : Nat)) = false := hl
      rw [(MathVal.eq_iff _ _).2 (by simp [e1])] at this
      cases this
    have hss : ss ≠ [] := fun e => by
      have := hlong e0 (List.mem_of_getElem? he0) hl0
      simp [e] at this
    obtain ⟨n, hn, hcp⟩ := PropSets.strings_of_propertyValue hpv hss
    have e67 : Ecma.Unicode.stringPropertyNames.map Prod.fst = Model.stringPropertyNames := rfl
    refine ⟨n, e67 ▸ hn, fun q => ?_⟩
    have : p = Model.codePointsOf Impl n := by
      apply Array.ext'
      rw [hp, codePointsOf_eq, ← hcp]
      simp [Function.comp_def]
    rw [this]
  normalize_points f xs _ := by
    have := points_isPoint _ (Engine.normalizePoints_le f (xs.toList.filterMap MathVal.idx))
    apply allPoints_of
    intro x hx
    have hx : x ∈ (Engine.normalizePoints f (xs.toList.filterMap MathVal.idx)).map fun (c : Nat) => MathVal.int c := by
      simpa using hx
    obtain ⟨c, hm, rfl⟩ := List.mem_map.1 hx
    exact ⟨c, Engine.normalizePoints_le f _ c hm, rfl⟩

end Engine.Impl
