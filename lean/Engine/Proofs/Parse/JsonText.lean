module

public import Engine.Proofs.Parse.Tables
public import Engine.Model.Parse

@[expose] public section

/-!
# Completeness of `Engine.JsonText.text` and span monotonicity for `codeAlphabet`

1. Proves unconditional span monotonicity (`i ≤ j`) and `slice` decomposition for `Step` and `Seq`
   over `codeAlphabet P` (shared with `Engine.Proofs.Parse.Code`).
2. Proves `jsonText_complete` and `noJSON_complete`: every derivation of `JSONText` in `.json` over
   `codeAlphabet P` is accepted by `Engine.JsonText.text`, so `Engine.noJSON` only rejects inputs
   that have no `.json` parse.
-/

namespace Engine.Parse

open Ecma.Grammar

/-! ## Tree size measure & unconditional span monotonicity over `codeAlphabet` -/

/-- Structural size of a `Grammar.Tree` for non-mutual recursion over `Step`/`Seq`. -/
def treeSize : Tree → Nat
  | .leaf _ _ => 1
  | .lex _ t => treeSize t + 1
  | .node _ _ _ _ _ kids => treeListSize kids + 1
where
  treeListSize : List Tree → Nat
    | [] => 0
    | t :: ts => treeSize t + treeListSize ts + 1

theorem codeTerm_nonempty {P : CodePrims} {s : Src} {k : Nat} {x : Terminal} {w : List Nat}
    (hok : codeLookTermOk x = true) (ht : (codeAlphabet P).term s k x w) : w ≠ [] := by
  cases x with
  | text str _ =>
    dsimp only [codeLookTermOk] at hok
    dsimp only [codeAlphabet] at ht
    intro hw
    rw [hw] at ht
    have hnil : str.toList = [] := List.map_eq_nil_iff.mp ht.symm
    have hstr : str = "" := by
      rw [← String.ofList_toList (s := str), hnil]
    subst hstr
    cases hok
  | cp n =>
    dsimp only [codeAlphabet] at ht
    cases hc : n.codePoint with
    | some v => rw [hc] at ht; rw [ht]; exact List.cons_ne_nil _ _
    | none => rw [hc] at ht; obtain ⟨c, rfl, _⟩ := ht; exact List.cons_ne_nil _ _

theorem slice_nonempty_lt {T : Type} {inp : List T} {i h : Nat} (hne : slice inp i h ≠ []) :
    i < h ∧ i < inp.length := by
  unfold slice at hne
  have h1 : i < h := Classical.byContradiction fun hge => by
    have hz : h - i = 0 := by omega
    rw [hz, List.take_zero] at hne
    exact hne rfl
  have h2 : i < inp.length := Classical.byContradiction fun hge => by
    have hd : inp.drop i = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd, List.take_nil] at hne
    exact hne rfl
  exact ⟨h1, h2⟩

theorem slice_eq_iff_drop {T : Type} {inp w : List T} {i h : Nat}
    (hle : i ≤ h) (hh : h ≤ inp.length) :
    slice inp i h = w ↔ w.length = h - i ∧ inp.drop i = w ++ inp.drop h := by
  unfold slice
  constructor
  · rintro rfl
    have hlen : ((inp.drop i).take (h - i)).length = h - i := by
      rw [List.length_take, List.length_drop]
      omega
    refine ⟨hlen, ?_⟩
    have hd : inp.drop h = (inp.drop i).drop (h - i) := by
      rw [List.drop_drop, Nat.add_sub_cancel' hle]
    rw [hd, List.take_append_drop]
  · rintro ⟨hlen, hdrop⟩
    rw [hdrop, ← hlen, List.take_left]

theorem slice_singleton_iff {T : Type} {inp : List T} {i h : Nat} {c : T}
    (hle : i ≤ h) (hh : h ≤ inp.length) :
    slice inp i h = [c] ↔ h = i + 1 ∧ inp[i]? = some c ∧ inp.drop i = c :: inp.drop (i + 1) := by
  rw [slice_eq_iff_drop hle hh]
  simp only [List.length_singleton, List.singleton_append]
  constructor
  · rintro ⟨hlen, hdrop⟩
    have hhi : h = i + 1 := by omega
    subst hhi
    have hget : inp[i]? = some c := by
      have hd0 : (inp.drop i)[0]? = inp[i]? := by simp
      rw [← hd0, hdrop]; rfl
    exact ⟨rfl, hget, hdrop⟩
  · rintro ⟨rfl, _, hdrop⟩
    exact ⟨by omega, hdrop⟩

private theorem code_step_seq_le (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {cx : Ctx} {g : GrammarId} :
    ∀ (sz : Nat),
      (∀ {n ps i j t}, treeSize t ≤ sz →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps i j t → i ≤ j) ∧
      (∀ {s ps k is i j m ts}, treeSize.treeListSize ts ≤ sz →
        (∀ it ∈ is, srcItemTermOk it = true) →
        Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is i j m ts → i ≤ j) := by
  intro sz
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    have hstep : ∀ {n ps i j t}, treeSize t ≤ sz →
        Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps i j t → i ≤ j := by
      intro n ps i j t hsz hs
      cases hs with
      | lex _ _ hleaf => cases hleaf
      | node s hsMem _ _ hseq =>
        dsimp only [treeSize] at hsz
        exact (ih _ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hsz)).2 (Nat.le_refl _)
          (fun it hit => srcItemTermOk_of_mem hok hsMem hit) hseq
    refine ⟨hstep, ?_⟩
    intro s ps k is
    induction is generalizing k with
    | nil =>
      intro i j m ts _ _ hseq
      cases hseq
      exact Nat.le_refl _
    | cons it rest ihs =>
      intro i j m ts hsz htok hseq
      have htokRest : ∀ x ∈ rest, srcItemTermOk x = true :=
        fun x hx => htok x (List.mem_cons_of_mem _ hx)
      cases hseq with
      | absent hrest =>
        exact ihs hsz htokRest hrest
      | term ht hrest =>
        have hok0 : codeLookTermOk _ = true := htok _ List.mem_cons_self
        have hlt := (slice_nonempty_lt (codeTerm_nonempty hok0 ht)).1
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hle2 := ihs (by omega) htokRest hrest
        omega
      | nt hst _ hrest =>
        dsimp only [treeSize.treeListSize] at hsz
        have hle1 := hstep (by omega) hst
        have hle2 := ihs (by omega) htokRest hrest
        omega
      | butNotT ht _ hrest =>
        have hok0 : codeLookTermOk _ = true := htok _ List.mem_cons_self
        have hlt := (slice_nonempty_lt (codeTerm_nonempty hok0 ht)).1
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hle2 := ihs (by omega) htokRest hrest
        omega
      | butNotN hst _ hrest =>
        dsimp only [treeSize.treeListSize] at hsz
        have hle1 := hstep (by omega) hst
        have hle2 := ihs (by omega) htokRest hrest
        omega
      | phrase hp hrest =>
        obtain ⟨c, hsc, _⟩ := hp
        have hlt := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
        dsimp only [treeSize.treeListSize, treeSize] at hsz
        have hle2 := ihs (by omega) htokRest hrest
        omega
      | look _ hrest =>
        exact ihs hsz htokRest hrest
      | noLT _ hrest =>
        exact ihs hsz htokRest hrest
      | empty hrest =>
        exact ihs hsz htokRest hrest
      | onlyIf hrest =>
        exact ihs hsz htokRest hrest

theorem code_step_le (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {cx : Ctx} {g : GrammarId}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    (hs : Step (codeAlphabet P) neg inp Ecma.Spec.gl cx g n ps i j t) : i ≤ j :=
  (code_step_seq_le hok (treeSize t)).1 (Nat.le_refl _) hs

theorem code_seq_le (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {inp : List Nat} {cx : Ctx} {g : GrammarId}
    {s : Src} {ps : List Param} {k : Nat} {is : List Item} {i j : Nat} {m : List Bool} {ts : List Tree}
    (htok : ∀ it ∈ is, srcItemTermOk it = true)
    (hs : Seq (codeAlphabet P) neg inp Ecma.Spec.gl cx g s ps k is i j m ts) : i ≤ j :=
  (code_step_seq_le hok (treeSize.treeListSize ts)).2 (Nat.le_refl _) htok hs

/-! ## JSON grammar alternatives and `JsonText` recognizer completeness -/

namespace JsonProof

open Engine.JsonText

def natT : CpTests Nat := ⟨(· == ·), (· < ·)⟩

/-- Non-dependent projection of `Rest l`. -/
def rval {α : Type} {l : List α} (o : Rest l) : Option (List α) := o.map Subtype.val

@[simp] private theorem rval_none {α : Type} {l : List α} : rval (none : Rest l) = none := rfl
@[simp] private theorem rval_some {α : Type} {l : List α} (v : List α) (h : v.length < l.length) :
    rval (some ⟨v, h⟩ : Rest l) = some v := rfl

@[simp] private theorem rval_lift {α : Type} {xs ys : List α} (h : ys.length ≤ xs.length) (p : Rest ys) :
    rval (lift h p) = rval p := by
  cases p <;> rfl

@[simp] private theorem rval_or {α : Type} {xs : List α} (p q : Rest xs) :
    rval (p.or q) = (rval p).or (rval q) := by
  cases p <;> cases q <;> rfl

@[simp] private theorem rval_seq {α : Type} {xs : List α} (p : Rest xs) (q : (ys : List α) → Rest ys) :
    rval (seq p q) = (rval p).bind (fun r => rval (q r)) := by
  cases p with
  | none => rfl
  | some v => rcases v with ⟨r, hr⟩; simp [seq]

@[simp] private theorem rval_seqOpt {α : Type} {xs : List α} (p : Rest xs) (q : (ys : List α) → Opt ys) :
    rval (seqOpt p q) = (rval p).map (fun r => (q r).1) := by
  cases p <;> rfl

@[simp] private theorem rval_optSeq {α : Type} {xs : List α} (p : Opt xs) (q : (ys : List α) → Rest ys) :
    rval (optSeq p q) = rval (q p.1) := by
  simp [optSeq]

@[simp] private theorem opt_val {α : Type} {xs : List α} (p : (ys : List α) → Rest ys) :
    (opt p xs).1 = (rval (p xs)).getD xs := by
  unfold opt
  cases p xs with
  | none => rfl
  | some v => rcases v with ⟨r, hr⟩; rfl

@[simp] private theorem rval_cp_cons (n c : Nat) (cs : List Nat) :
    rval (cp natT n (c :: cs)) = if c == n then some cs else none := by
  unfold cp natT; dsimp only; split <;> rfl

@[simp] private theorem rval_cpOf_cons (pred : Nat → Bool) (c : Nat) (cs : List Nat) :
    rval (cpOf pred (c :: cs)) = if pred c then some cs else none := by
  unfold cpOf; dsimp only; split <;> rfl

private theorem term_one_char {P : CodePrims} {xs : List Nat} {s : Src} {k : Nat}
    {str : String} {b : Bool} {i h j c : Nat}
    (hc : str.toList.map Char.toNat = [c]) (hle : h ≤ j) (hj : j ≤ xs.length)
    (ht : (codeAlphabet P).term s k (.text str b) (slice xs i h)) :
    h = i + 1 ∧ xs.drop i = c :: xs.drop (i + 1) := by
  dsimp only [codeAlphabet] at ht
  rw [hc] at ht
  have h1 : i ≤ h := Nat.le_of_lt (slice_nonempty_lt (by rw [ht]; exact List.cons_ne_nil _ _)).1
  obtain ⟨rfl, _, hdrop⟩ := (slice_singleton_iff h1 (by omega)).mp ht
  exact ⟨rfl, hdrop⟩

private theorem rval_cps_exact : ∀ (ns rest : List Nat), ns ≠ [] →
    rval (cps natT ns (ns ++ rest)) = some rest
  | [], _, hne => absurd rfl hne
  | [n], rest, _ => by unfold cps natT; simp
  | n :: m :: ms, rest, _ => by
    have ih := rval_cps_exact (m :: ms) rest (List.cons_ne_nil _ _)
    rw [List.cons_append, cps]
    have hnn : (!natT.is n n) = false := by simp [natT]
    rw [hnn]
    simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons, rval_lift]
    exact ih

private theorem json_rules_eq : Ecma.Spec.gl.rulesOf .json = Gen.JSON.rules := rfl

private theorem json_pinned_eq (n : NT) :
    Ecma.Spec.gl.pinned .json n = ((Gen.JSON.rules.find? (·.lhs == n)).map (srcsOf .json)).getD [] := by
  unfold GL.pinned baseGrammar
  rw [json_rules_eq]
  cases List.find? (·.lhs == n) Gen.JSON.rules <;> rfl

private theorem json_alts_eq (hok : parseTablesOk = true) (cx : Ctx) (n : NT) :
    Ecma.Spec.gl.alts cx .json n = ((Gen.JSON.rules.find? (·.lhs == n)).map (srcsOf .json)).getD [] := by
  rw [(fast_invariants hok cx).2.2.2.2.2.2.2.2 n, json_pinned_eq]

private theorem json_alts_rule (hok : parseTablesOk = true) (cx : Ctx) (n : NT) {r : Rule}
    (hr : ((Gen.JSON.rules.find? (·.lhs == n)).map (srcsOf .json)).getD [] = srcsOf .json r) :
    Ecma.Spec.gl.alts cx .json n = srcsOf .json r :=
  (json_alts_eq hok cx n).trans hr

private theorem mem_of_mem_zipIdx {α : Type} : ∀ {xs : List α} {a : α} {i k : Nat},
    (a, i) ∈ xs.zipIdx k → a ∈ xs
  | [], _, _, _, h => by cases h
  | x :: xs, a, _, _, h => by
    rcases List.mem_cons.mp h with heq | htl
    · injection heq with hax _; subst hax; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_mem_zipIdx htl)

private theorem srcsOf_oneOf_mem {g : GrammarId} {lhs : NT} {ps : List Param} {col : Colons}
    {rows : List (List Terminal)} {s : Src}
    (hs : s ∈ srcsOf g ⟨lhs, ps, col, .oneOf rows⟩) :
    ∃ x ∈ rows.flatten, s.alt.rhs = [.sym (.t x) false] := by
  unfold srcsOf writtenAlts at hs
  rw [List.mem_map] at hs
  obtain ⟨⟨a, idx⟩, hmem, rfl⟩ := hs
  have ha : a ∈ rows.flatten.map (fun x => (⟨[], [.sym (.t x) false], none⟩ : Alt)) :=
    mem_of_mem_zipIdx hmem
  rw [List.mem_map] at ha
  obtain ⟨x, hx, rfl⟩ := ha
  exact ⟨x, hx, rfl⟩

private theorem step_oneOf_char (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {n : NT} {ps : List Param} {i j : Nat} {t : Tree}
    {rows : List (List Terminal)}
    (hr : ((Gen.JSON.rules.find? (·.lhs == n)).map (srcsOf .json)).getD [] =
      srcsOf .json ⟨n, [], .two, .oneOf rows⟩)
    (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json n ps i j t)
    {pred : Nat → Bool}
    (hpred : ∀ x ∈ rows.flatten, ∀ w, (codeAlphabet P).term (⟨.json, ⟨n, [], .two, .oneOf rows⟩, 0, ⟨[], [], none⟩⟩) 0 x w →
      ∃ c, w = [c] ∧ pred c = true) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ pred c = true := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx n hr] at hsMem
    obtain ⟨x, hx, hrhs⟩ := srcsOf_oneOf_mem hsMem
    rw [hrhs] at hseq
    cases hseq with
    | term ht hnil =>
      cases hnil with
      | nil =>
        have htermEq : (codeAlphabet P).term ⟨.json, ⟨n, [], .two, .oneOf rows⟩, 0, ⟨[], [], none⟩⟩ 0 x (slice xs i j) := ht
        obtain ⟨c, hsc, hpc⟩ := hpred x hx _ htermEq
        have hle : i ≤ j := by
          have := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
          omega
        obtain ⟨rfl, _, hdrop⟩ := (slice_singleton_iff hle hj).mp hsc
        exact ⟨rfl, c, hdrop, hpc⟩

private theorem inRange_natT (c lo hi : Nat) :
    inRange natT c lo hi = decide (lo ≤ c ∧ c ≤ hi) := by
  unfold inRange natT
  by_cases h1 : c < lo
  · have h2 : ¬ (lo ≤ c ∧ c ≤ hi) := by omega
    simp [h1, h2]
  · by_cases h2 : c < hi + 1
    · have h3 : lo ≤ c ∧ c ≤ hi := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (lo ≤ c ∧ c ≤ hi) := by omega
      simp [h1, h2, h3]

private theorem wsChar_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONWhiteSpaceCharacter ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isWhiteSpaceCharacter natT c = true := by
  refine step_oneOf_char hok rfl hj hs fun x hx w htw => ?_
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨0x09, htw, by decide⟩
  · exact ⟨0x0A, htw, by decide⟩
  · exact ⟨0x0D, htw, by decide⟩
  · exact ⟨0x20, htw, by decide⟩

private theorem oneOf_text_pred {P : CodePrims} {n : NT} {rows : List (List Terminal)}
    {pred : Nat → Bool}
    (hall : rows.flatten.all (fun t => match t with
      | .text s _ => match s.toList.map Char.toNat with
        | [c] => pred c
        | _ => false
      | _ => false) = true)
    {x : Terminal} (hx : x ∈ rows.flatten) {w : List Nat}
    (htw : (codeAlphabet P).term ⟨.json, ⟨n, [], .two, .oneOf rows⟩, 0, ⟨[], [], none⟩⟩ 0 x w) :
    ∃ c, w = [c] ∧ pred c = true := by
  have hb := List.all_eq_true.mp hall x hx
  cases x with
  | cp _ => cases hb
  | text str _ =>
    dsimp only [codeAlphabet] at htw; rw [htw]
    cases hm : str.toList.map Char.toNat with
    | nil => simp [hm] at hb
    | cons c tl =>
      cases tl with
      | nil => simp [hm] at hb; exact ⟨c, rfl, hb⟩
      | cons _ _ => simp [hm] at hb

private theorem digit_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONDigit ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isDigit natT c = true :=
  step_oneOf_char hok rfl hj hs fun _ hx _ htw => oneOf_text_pred (by decide) hx htw

private theorem nonZeroDigit_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONNonZeroDigit ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isNonZeroDigit natT c = true :=
  step_oneOf_char hok rfl hj hs fun _ hx _ htw => oneOf_text_pred (by decide) hx htw

private theorem expInd_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONExponentIndicator ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isExponentIndicator natT c = true :=
  step_oneOf_char hok rfl hj hs fun _ hx _ htw => oneOf_text_pred (by decide) hx htw

private theorem sign_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONSign ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isSign natT c = true :=
  step_oneOf_char hok rfl hj hs fun _ hx _ htw => oneOf_text_pred (by decide) hx htw

private theorem singleEsc_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONSingleEscapeCharacter ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isSingleEscapeCharacter natT c = true :=
  step_oneOf_char hok rfl hj hs fun _ hx _ htw => oneOf_text_pred (by decide) hx htw

private theorem hexDigit_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONHexDigit ps i j t) :
    j = i + 1 ∧ ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isHexDigit natT c = true :=
  step_oneOf_char hok rfl hj hs fun _ hx _ htw => oneOf_text_pred (by decide) hx htw

private theorem controlChar_derives (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {i : Nat} {c : Nat} (hi : i + 1 ≤ xs.length) (hdrop : xs.drop i = c :: xs.drop (i + 1))
    (hc : isControlCharacter natT c = true) :
    ∃ t, Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONControlCharacter [] i (i + 1) t := by
  have hlt : c < 32 := by simpa [isControlCharacter, natT] using hc
  have hcheck : (List.range 32).all (fun k =>
      (srcsOf .json Gen.JSON.JSONControlCharacter).any fun s =>
        s.alt.guard.isEmpty && match s.alt.rhs with
          | [.sym (.t (.text str false)) false] => str.toList.map Char.toNat == [k]
          | _ => false) = true := by decide
  have hcMem := List.all_eq_true.mp hcheck c (List.mem_range.mpr hlt)
  obtain ⟨s, hsMem, hsOk⟩ := List.any_eq_true.mp hcMem
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hsOk
  obtain ⟨hgrd, hrhsOk⟩ := hsOk
  have hsAlts : s ∈ Ecma.Spec.gl.alts cx .json .JSONControlCharacter := by
    rw [json_alts_rule hok cx .JSONControlCharacter rfl]; exact hsMem
  obtain ⟨_, hopts⟩ := alt_lhs_and_opts hok hsAlts
  have hrhsEx : ∃ str, s.alt.rhs = [.sym (.t (.text str false)) false] ∧ str.toList.map Char.toNat = [c] := by
    cases hr0 : s.alt.rhs with
    | nil => rw [hr0] at hrhsOk; cases hrhsOk
    | cons it0 rest0 =>
      rw [hr0] at hrhsOk
      cases rest0 with
      | cons _ _ =>
        cases it0 with
        | sym sym opt =>
          cases sym with
          | nt _ _ => cases hrhsOk
          | t tm =>
            cases tm with
            | cp _ => cases hrhsOk
            | text _ csSense => cases csSense <;> cases opt <;> cases hrhsOk
        | _ => cases hrhsOk
      | nil =>
        cases it0 with
        | sym sym opt =>
          cases sym with
          | nt _ _ => cases hrhsOk
          | t term =>
            cases term with
            | cp _ => cases hrhsOk
            | text str csSense =>
              cases csSense <;> cases opt <;> dsimp only at hrhsOk <;> try cases hrhsOk
              exact ⟨str, rfl, beq_iff_eq.mp hrhsOk⟩
        | _ => cases hrhsOk
  obtain ⟨str, hrhs, hrhsEq⟩ := hrhsEx
  have hopts0 : s.alt.opts = 0 := by rw [hopts, hrhs]; rfl
  have hm0 : ([] : List Bool) ∈ masks s.alt.opts := by rw [hopts0]; decide
  obtain ⟨_, id, _, hid, _⟩ := prodIdOf_spec hok hsAlts hm0
  have hslice : slice xs i (i + 1) = [c] :=
    (slice_singleton_iff (by omega) hi).mpr ⟨rfl, by
      have hd0 : (xs.drop i)[0]? = xs[i]? := by simp
      rw [← hd0, hdrop]; rfl, hdrop⟩
  have hterm : (codeAlphabet P).term s 0 (.text str false) (slice xs i (i + 1)) := by
    dsimp only [codeAlphabet]; rw [hslice, hrhsEq]
  have hseq : Seq (codeAlphabet P) neg xs Ecma.Spec.gl cx .json s [] 0 s.alt.rhs i (i + 1) [] [.leaf i (i + 1)] := by
    rw [hrhs]; exact .term hterm .nil
  have hgrdAll : s.alt.guard.all (Guard.holds []) = true := by rw [hgrd]; rfl
  exact ⟨_, Step.node s hsAlts hgrdAll hid hseq⟩

/-! ### Non-dependent recognizer equations -/

private theorem whiteSpace_eq_self {l : List Nat}
    (hno : ∀ c cs, l = c :: cs → isWhiteSpaceCharacter natT c = false) :
    (whiteSpace natT l).1 = l := by
  cases l with
  | nil => rfl
  | cons c cs => simp [whiteSpace, hno c cs rfl]

private theorem whiteSpace_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hno : ∀ c cs, xs.drop j = c :: cs → isWhiteSpaceCharacter natT c = false)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONWhiteSpace ps i j t) :
    i < j ∧ (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isWhiteSpaceCharacter natT c = true) ∧
      (whiteSpace natT (xs.drop i)).1 = xs.drop j := by
  induction hsz : treeSize t using Nat.strongRecOn generalizing i j t ps with
  | ind sz ih =>
    subst hsz
    cases hs with
    | lex _ _ hl => cases hl
    | node s hsMem _ _ hseq =>
      rw [json_alts_rule hok cx .JSONWhiteSpace rfl] at hsMem
      simp only [srcsOf, writtenAlts, Gen.JSON.JSONWhiteSpace, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.mem_singleton] at hsMem
      subst hsMem
      cases hseq with
      | nt hws _ hrest =>
        have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl; rfl) hrest
        obtain ⟨rfl, c, hdrop, hwc⟩ := wsChar_step hok (by omega) hws
        cases hrest with
        | absent hnil =>
          cases hnil
          refine ⟨by omega, ⟨c, hdrop, hwc⟩, ?_⟩
          rw [hdrop]; simp [whiteSpace, hwc, whiteSpace_eq_self hno]
        | nt hws2 _ hnil =>
          cases hnil
          dsimp only [treeSize, treeSize.treeListSize] at ih
          obtain ⟨hlt2, _, hrec⟩ := ih (treeSize _) (by omega) hj hno hws2 rfl
          refine ⟨by omega, ⟨c, hdrop, hwc⟩, ?_⟩
          rw [hdrop]; simp [whiteSpace, hwc, hrec]

private theorem whiteSpace_chars (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {a b : Nat} {t : Tree} (hb : b ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONWhiteSpace ps a b t) :
    ∀ p, a ≤ p → p < b → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true := by
  induction hsz : treeSize t using Nat.strongRecOn generalizing a b t ps with
  | ind sz ih =>
    subst hsz
    cases hs with
    | lex _ _ hl => cases hl
    | node s hsMem _ _ hseq =>
      rw [json_alts_rule hok cx .JSONWhiteSpace rfl] at hsMem
      simp only [srcsOf, writtenAlts, Gen.JSON.JSONWhiteSpace, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.mem_singleton] at hsMem
      subst hsMem
      cases hseq with
      | nt hwc _ hrest =>
        have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl; rfl) hrest
        obtain ⟨rfl, cw, hdcw, hwcw⟩ := wsChar_step hok (by omega) hwc
        intro p hap hpb
        by_cases hp : p = a
        · subst hp; exact ⟨cw, hdcw, hwcw⟩
        · cases hrest with
          | absent hnil => cases hnil; omega
          | nt hw2 _ hnil =>
            cases hnil
            dsimp only [treeSize, treeSize.treeListSize] at ih
            exact ih (treeSize _) (by omega) hb hw2 rfl p (by omega) hpb

private theorem rval_digits_none {l : List Nat}
    (hno : ∀ c cs, l = c :: cs → isDigit natT c = false) :
    rval (digits natT l) = none := by
  cases l with
  | nil => rfl
  | cons c cs => simp [digits, hno c cs rfl]

private theorem rval_digits_cons (c : Nat) (cs : List Nat) :
    rval (digits natT (c :: cs)) =
      if !isDigit natT c then none else (rval (digits natT cs)).or (some cs) := by
  simp only [digits]
  split
  · rfl
  · cases digits natT cs <;> rfl

private theorem digits_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hno : ∀ c cs, xs.drop j = c :: cs → isDigit natT c = false)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONDigits ps i j t) :
    (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isDigit natT c = true) ∧
      rval (digits natT (xs.drop i)) = some (xs.drop j) := by
  induction hsz : treeSize t using Nat.strongRecOn generalizing i j t ps with
  | ind sz ih =>
    subst hsz
    cases hs with
    | lex _ _ hl => cases hl
    | node s hsMem _ _ hseq =>
      rw [json_alts_rule hok cx .JSONDigits rfl] at hsMem
      simp only [srcsOf, writtenAlts, Gen.JSON.JSONDigits, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.mem_singleton] at hsMem
      subst hsMem
      cases hseq with
      | nt hd1 _ hrest =>
        have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl; rfl) hrest
        obtain ⟨rfl, c, hdrop, hdc⟩ := digit_step hok (by omega) hd1
        cases hrest with
        | absent hnil =>
          cases hnil
          refine ⟨⟨c, hdrop, hdc⟩, ?_⟩
          rw [hdrop, rval_digits_cons, hdc, rval_digits_none hno]; rfl
        | nt hd2 _ hnil =>
          cases hnil
          dsimp only [treeSize, treeSize.treeListSize] at ih
          obtain ⟨_, hrec⟩ := ih (treeSize _) (by omega) hj hno hd2 rfl
          refine ⟨⟨c, hdrop, hdc⟩, ?_⟩
          rw [hdrop, rval_digits_cons, hdc, hrec]; rfl

private theorem integer_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hno : ∀ c cs, xs.drop j = c :: cs → isDigit natT c = false)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONInteger ps i j t) :
    i < j ∧ (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isDigit natT c = true) ∧
      rval (integer natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONInteger rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONInteger, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
    rcases hsMem with rfl | rfl
    · cases hseq with
      | term ht hnil =>
        cases hnil
        dsimp only [codeAlphabet] at ht
        have hsc : slice xs i j = [0x30] := ht
        have hle : i ≤ j := Nat.le_of_lt (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1
        obtain ⟨rfl, _, hdrop⟩ := (slice_singleton_iff hle hj).mp hsc
        refine ⟨by omega, ⟨0x30, hdrop, by decide⟩, ?_⟩
        unfold integer
        rw [hdrop]; simp
    · cases hseq with
      | nt hnz _ hrest =>
        have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl; rfl) hrest
        obtain ⟨rfl, c, hdrop, hnzc⟩ := nonZeroDigit_step hok (by omega) hnz
        have hdc : isDigit natT c = true := by
          rw [isNonZeroDigit, inRange_natT] at hnzc
          rw [isDigit, inRange_natT]
          have := of_decide_eq_true hnzc
          exact decide_eq_true (by omega)
        have hne0 : (c == 0x30) = false := by
          rw [isNonZeroDigit, inRange_natT] at hnzc
          have := of_decide_eq_true hnzc
          rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; omega
        cases hrest with
        | absent hnil =>
          cases hnil
          refine ⟨by omega, ⟨c, hdrop, hdc⟩, ?_⟩
          unfold integer
          rw [hdrop]; simp only [rval_or, rval_cp_cons, hne0, Bool.false_eq_true, ↓reduceIte,
            rval_seqOpt, rval_cpOf_cons, hnzc, Option.none_or, Option.map_some, opt_val,
            rval_digits_none hno, Option.getD_none]
        | nt hds _ hnil =>
          cases hnil
          obtain ⟨_, hdigs⟩ := digits_step hok hj hno hds
          refine ⟨by omega, ⟨c, hdrop, hdc⟩, ?_⟩
          unfold integer
          rw [hdrop]; simp only [rval_or, rval_cp_cons, hne0, Bool.false_eq_true, ↓reduceIte,
            rval_seqOpt, rval_cpOf_cons, hnzc, Option.none_or, Option.map_some, opt_val,
            hdigs, Option.getD_some]

private theorem rval_fraction_none {l : List Nat} (hno : ∀ c cs, l = c :: cs → c ≠ 0x2E) :
    rval (fraction natT l) = none := by
  cases l with
  | nil => rfl
  | cons c cs =>
    have hne : (c == 0x2E) = false := by rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; exact hno c cs rfl
    simp [fraction, hne]

private theorem fraction_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hno : ∀ c cs, xs.drop j = c :: cs → isDigit natT c = false)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONFraction ps i j t) :
    xs.drop i = 0x2E :: xs.drop (i + 1) ∧
      rval (fraction natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONFraction rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONFraction, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hsMem
    subst hsMem
    cases hseq with
    | term ht hrest =>
      cases hrest with
      | nt hds _ hnil =>
        cases hnil
        obtain ⟨rfl, hdrop⟩ := term_one_char (c := 0x2E) rfl (code_step_le hok hds) hj ht
        obtain ⟨_, hdigs⟩ := digits_step hok hj hno hds
        refine ⟨hdrop, ?_⟩
        unfold fraction
        rw [hdrop]; simp [hdigs]

private theorem rval_exponent_none {l : List Nat}
    (hno : ∀ c cs, l = c :: cs → isExponentIndicator natT c = false) :
    rval (exponent natT l) = none := by
  cases l with
  | nil => rfl
  | cons c cs => simp [exponent, hno c cs rfl]

private theorem exponent_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hno : ∀ c cs, xs.drop j = c :: cs → isDigit natT c = false)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONExponent ps i j t) :
    (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isExponentIndicator natT c = true) ∧
      rval (exponent natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONExponent rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONExponent, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hsMem
    subst hsMem
    cases hseq with
    | nt hexp _ hrest =>
      have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hrest
      obtain ⟨rfl, ce, hdropE, hce⟩ := expInd_step hok (by omega) hexp
      cases hrest with
      | absent hrest2 =>
        cases hrest2 with
        | nt hds _ hnil =>
          cases hnil
          obtain ⟨⟨cd, hdropD, hdcd⟩, hdigs⟩ := digits_step hok hj hno hds
          have hnsign : isSign natT cd = false := by
            rw [isDigit, inRange_natT] at hdcd
            have := of_decide_eq_true hdcd
            unfold isSign natT
            rw [Bool.or_eq_false_iff]; simp; omega
          have hoptS : (opt (cpOf (isSign natT)) (xs.drop (i + 1))).1 = xs.drop (i + 1) := by
            rw [opt_val, hdropD]; simp [hnsign]
          refine ⟨⟨ce, hdropE, hce⟩, ?_⟩
          unfold exponent
          rw [hdropE]; simp only [rval_seq, rval_cpOf_cons, hce, ↓reduceIte, Option.bind_some, rval_optSeq]
          rw [hoptS, hdigs]
      | nt hsg _ hrest2 =>
        cases hrest2 with
        | nt hds _ hnil =>
          cases hnil
          have hleDs := code_step_le hok hds
          obtain ⟨rfl, csgn, hdropS, hcsgn⟩ := sign_step hok (by omega) hsg
          obtain ⟨_, hdigs⟩ := digits_step hok hj hno hds
          have hoptS : (opt (cpOf (isSign natT)) (xs.drop (i + 1))).1 = xs.drop (i + 1 + 1) := by
            rw [opt_val, hdropS]; simp [hcsgn]
          refine ⟨⟨ce, hdropE, hce⟩, ?_⟩
          unfold exponent
          rw [hdropE]; simp only [rval_seq, rval_cpOf_cons, hce, ↓reduceIte, Option.bind_some, rval_optSeq]
          rw [hoptS, hdigs]

/-- Valid delimiters after a `JSONValue` (`ws`, `,`, `}`, `]`, or EOF). -/
def ValDelim (r : List Nat) : Prop :=
  ∀ c cs, r = c :: cs →
    c = 0x09 ∨ c = 0x0A ∨ c = 0x0D ∨ c = 0x20 ∨ c = 0x2C ∨ c = 0x7D ∨ c = 0x5D

/-- Valid delimiters after a `JSONElement` (`,`, `}`, `]`, or EOF). -/
def ElemDelim (r : List Nat) : Prop :=
  ∀ c cs, r = c :: cs → c = 0x2C ∨ c = 0x7D ∨ c = 0x5D

private theorem valDelim_not_digit {r : List Nat} (hd : ValDelim r) :
    ∀ c cs, r = c :: cs → isDigit natT c = false := by
  intro c cs hr
  rw [isDigit, inRange_natT, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
  rcases hd c cs hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem valDelim_not_dot {r : List Nat} (hd : ValDelim r) :
    ∀ c cs, r = c :: cs → c ≠ 0x2E := by
  intro c cs hr
  rcases hd c cs hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem valDelim_not_exp {r : List Nat} (hd : ValDelim r) :
    ∀ c cs, r = c :: cs → isExponentIndicator natT c = false := by
  intro c cs hr
  rcases hd c cs hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem elemDelim_valDelim {r : List Nat} (hd : ElemDelim r) : ValDelim r := by
  intro c cs hr
  rcases hd c cs hr with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

private theorem elemDelim_not_ws {r : List Nat} (hd : ElemDelim r) :
    ∀ c cs, r = c :: cs → isWhiteSpaceCharacter natT c = false := by
  intro c cs hr
  rcases hd c cs hr with rfl | rfl | rfl <;> decide

private theorem rval_number_eq {l r1 r2 r3 : List Nat}
    (h0 : (opt (cp natT 0x2D) l).1 = r1)
    (h1 : rval (integer natT r1) = some r2)
    (h2 : (opt (fraction natT) r2).1 = r3) :
    rval (number natT l) = some (opt (exponent natT) r3).1 := by
  unfold number
  simp only [rval_seqOpt, rval_optSeq]
  rw [h0, h1]
  simp only [Option.map_some, h2]

private theorem rval_number_none_of_char {c : Nat} {cs : List Nat}
    (hneM : (c == 0x2D) = false) (hne0 : (c == 0x30) = false) (hnz : isNonZeroDigit natT c = false) :
    rval (number natT (c :: cs)) = none := by
  unfold number integer
  simp only [rval_seqOpt, rval_optSeq]
  have hopt : (opt (cp natT 0x2D) (c :: cs)).1 = c :: cs := by rw [opt_val]; simp [hneM]
  rw [hopt]
  simp [hne0, hnz]

private theorem seq_nt_inv {α : Type} {A : Alphabet α} {neg : NT → List Param → Nat → Nat → Prop} {inp : List α}
    {gl : GL} {cx : Ctx} {g : GrammarId} {s : Src} {ps : List Param} {k : Nat}
    {m : NT} {args : List Arg} {o : Bool} {rest : List Item} {i j : Nat} {ms : List Bool} {ts : List Tree}
    (hseq : Seq A neg inp gl cx g s ps k (.sym (.nt m args) o :: rest) i j ms ts) :
    (o = true ∧ ∃ ms', ms = false :: ms' ∧ Seq A neg inp gl cx g s ps (k + 1) rest i j ms' ts) ∨
    ∃ h t ms' ts', ms = (if o then true :: ms' else ms') ∧ ts = t :: ts' ∧
      CondOk A inp rest t ∧ Step A neg inp gl cx g m (applyArgs ps args) i h t ∧
      Seq A neg inp gl cx g s ps (k + 1) rest h j ms' ts' := by
  cases hseq with
  | absent hrest => exact Or.inl ⟨rfl, _, rfl, hrest⟩
  | nt hst hc hrest => exact Or.inr ⟨_, _, _, _, rfl, rfl, hc, hst, hrest⟩

private theorem number_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hvd : ValDelim (xs.drop j))
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONNumber ps i j t) :
    i < j ∧ (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ (c = 0x2D ∨ isDigit natT c = true)) ∧
      rval (number natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONNumber rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONNumber, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hsMem
    have htail : ∀ {k0 : Nat} {m0 : List Bool} {ts0 : List Tree},
        i ≤ k0 →
        ((k0 = i ∧ ∀ (hdig0 : ∃ c, xs.drop k0 = c :: xs.drop (k0 + 1) ∧ isDigit natT c = true),
            (opt (cp natT 0x2D) (xs.drop i)).1 = xs.drop k0 ∧
            ∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ (c = 0x2D ∨ isDigit natT c = true)) ∨
          (k0 = i + 1 ∧ xs.drop i = 0x2D :: xs.drop (i + 1) ∧
            (opt (cp natT 0x2D) (xs.drop i)).1 = xs.drop k0)) →
        Seq (codeAlphabet P) neg xs Ecma.Spec.gl cx .json s ps 1
          [.sym (.nt .JSONInteger []) false, .sym (.nt .JSONFraction []) true, .sym (.nt .JSONExponent []) true]
          k0 j m0 ts0 →
        i < j ∧ (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ (c = 0x2D ∨ isDigit natT c = true)) ∧
          rval (number natT (xs.drop i)) = some (xs.drop j) := by
      intro k0 m0 ts0 hik0 hsign hseq1
      rcases seq_nt_inv hseq1 with ⟨⟨⟩, _⟩ | ⟨k1, _, _, _, _, _, _, hint, hseq2⟩
      have hle2 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hseq2
      rcases seq_nt_inv hseq2 with ⟨_, _, _, hseq3⟩ | ⟨k2, _, _, _, _, _, _, hfr, hseq3⟩
      · cases hseq3 with
        | absent hnil =>
          cases hnil
          obtain ⟨hltI, hdig0, hintEq⟩ := integer_step hok hj (valDelim_not_digit hvd) hint
          have hfrO : (opt (fraction natT) (xs.drop j)).1 = xs.drop j := by
            rw [opt_val, rval_fraction_none (valDelim_not_dot hvd)]; rfl
          have hexO : (opt (exponent natT) (xs.drop j)).1 = xs.drop j := by
            rw [opt_val, rval_exponent_none (valDelim_not_exp hvd)]; rfl
          rcases hsign with ⟨rfl, hnoS⟩ | ⟨rfl, hdropM, hoptM⟩
          · obtain ⟨hopt0, hc0⟩ := hnoS hdig0
            exact ⟨hltI, hc0, (rval_number_eq hopt0 hintEq hfrO).trans (congrArg some hexO)⟩
          · exact ⟨by omega, ⟨0x2D, hdropM, Or.inl rfl⟩,
              (rval_number_eq hoptM hintEq hfrO).trans (congrArg some hexO)⟩
        | nt hexp _ hnil =>
          cases hnil
          have hleExp := code_step_le hok hexp
          obtain ⟨⟨ce, hdropE, hce⟩, hexpEq⟩ := exponent_step hok hj (valDelim_not_digit hvd) hexp
          have hnoDigK1 : ∀ c cs, xs.drop k1 = c :: cs → isDigit natT c = false := by
            intro c cs hr; rw [hdropE] at hr; cases hr
            unfold isExponentIndicator natT at hce
            simp only [Bool.or_eq_true, beq_iff_eq] at hce
            rw [isDigit, inRange_natT, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
            rcases hce with rfl | rfl <;> omega
          have hnoDotK1 : ∀ c cs, xs.drop k1 = c :: cs → c ≠ 0x2E := by
            intro c cs hr; rw [hdropE] at hr; cases hr
            unfold isExponentIndicator natT at hce
            simp only [Bool.or_eq_true, beq_iff_eq] at hce
            rcases hce with rfl | rfl <;> omega
          obtain ⟨hltI, hdig0, hintEq⟩ := integer_step hok (by omega) hnoDigK1 hint
          have hfrO : (opt (fraction natT) (xs.drop k1)).1 = xs.drop k1 := by
            rw [opt_val, rval_fraction_none hnoDotK1]; rfl
          have hexO : (opt (exponent natT) (xs.drop k1)).1 = xs.drop j := by
            rw [opt_val, hexpEq]; rfl
          rcases hsign with ⟨rfl, hnoS⟩ | ⟨rfl, hdropM, hoptM⟩
          · obtain ⟨hopt0, hc0⟩ := hnoS hdig0
            exact ⟨by omega, hc0, (rval_number_eq hopt0 hintEq hfrO).trans (congrArg some hexO)⟩
          · exact ⟨by omega, ⟨0x2D, hdropM, Or.inl rfl⟩,
              (rval_number_eq hoptM hintEq hfrO).trans (congrArg some hexO)⟩
      · have hleFr := code_step_le hok hfr
        cases hseq3 with
        | absent hnil =>
          cases hnil
          obtain ⟨hdropDot, hfrEq⟩ := fraction_step hok hj (valDelim_not_digit hvd) hfr
          have hnoDigK1 : ∀ c cs, xs.drop k1 = c :: cs → isDigit natT c = false := by
            intro c cs hr; rw [hdropDot] at hr; cases hr; unfold isDigit inRange natT; rfl
          obtain ⟨hltI, hdig0, hintEq⟩ := integer_step hok (by omega) hnoDigK1 hint
          have hfrO : (opt (fraction natT) (xs.drop k1)).1 = xs.drop j := by
            rw [opt_val, hfrEq]; rfl
          have hexO : (opt (exponent natT) (xs.drop j)).1 = xs.drop j := by
            rw [opt_val, rval_exponent_none (valDelim_not_exp hvd)]; rfl
          rcases hsign with ⟨rfl, hnoS⟩ | ⟨rfl, hdropM, hoptM⟩
          · obtain ⟨hopt0, hc0⟩ := hnoS hdig0
            exact ⟨by omega, hc0, (rval_number_eq hopt0 hintEq hfrO).trans (congrArg some hexO)⟩
          · exact ⟨by omega, ⟨0x2D, hdropM, Or.inl rfl⟩,
              (rval_number_eq hoptM hintEq hfrO).trans (congrArg some hexO)⟩
        | nt hexp _ hnil =>
          cases hnil
          have hleExp := code_step_le hok hexp
          obtain ⟨⟨ce, hdropE, hce⟩, hexpEq⟩ := exponent_step hok hj (valDelim_not_digit hvd) hexp
          have hnoDigK2 : ∀ c cs, xs.drop k2 = c :: cs → isDigit natT c = false := by
            intro c cs hr; rw [hdropE] at hr; cases hr
            unfold isExponentIndicator natT at hce
            simp only [Bool.or_eq_true, beq_iff_eq] at hce
            rw [isDigit, inRange_natT, Bool.eq_false_iff, ne_eq, decide_eq_true_eq]
            rcases hce with rfl | rfl <;> omega
          obtain ⟨hdropDot, hfrEq⟩ := fraction_step hok (by omega) hnoDigK2 hfr
          have hnoDigK1 : ∀ c cs, xs.drop k1 = c :: cs → isDigit natT c = false := by
            intro c cs hr; rw [hdropDot] at hr; cases hr; unfold isDigit inRange natT; rfl
          obtain ⟨hltI, hdig0, hintEq⟩ := integer_step hok (by omega) hnoDigK1 hint
          have hfrO : (opt (fraction natT) (xs.drop k1)).1 = xs.drop k2 := by
            rw [opt_val, hfrEq]; rfl
          have hexO : (opt (exponent natT) (xs.drop k2)).1 = xs.drop j := by
            rw [opt_val, hexpEq]; rfl
          rcases hsign with ⟨rfl, hnoS⟩ | ⟨rfl, hdropM, hoptM⟩
          · obtain ⟨hopt0, hc0⟩ := hnoS hdig0
            exact ⟨by omega, hc0, (rval_number_eq hopt0 hintEq hfrO).trans (congrArg some hexO)⟩
          · exact ⟨by omega, ⟨0x2D, hdropM, Or.inl rfl⟩,
              (rval_number_eq hoptM hintEq hfrO).trans (congrArg some hexO)⟩
    subst hsMem
    cases hseq with
    | absent hseq1 =>
      refine htail (Nat.le_refl _) (Or.inl ⟨rfl, fun ⟨c, hdropC, hdc⟩ => ?_⟩) hseq1
      have hneM : (c == 0x2D) = false := by
        rw [isDigit, inRange_natT] at hdc
        have := of_decide_eq_true hdc
        rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; omega
      exact ⟨by rw [opt_val, hdropC]; simp [hneM], ⟨c, hdropC, Or.inr hdc⟩⟩
    | term ht hseq1 =>
      have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl | rfl <;> rfl) hseq1
      obtain ⟨rfl, hdropM⟩ := term_one_char (c := 0x2D) rfl hleRest hj ht
      exact htail (by omega) (Or.inr ⟨rfl, hdropM, by rw [opt_val, hdropM]; simp⟩) hseq1

private theorem escape_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P) neg xs Ecma.Spec.gl cx .json .JSONEscape ps i j t) :
    rval (escape natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONEscape rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONEscape, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
    rcases hsMem with rfl | rfl
    · cases hseq with
      | nt hse _ hnil =>
        cases hnil
        obtain ⟨rfl, c, hdrop, hsec⟩ := singleEsc_step hok hj hse
        unfold escape; rw [hdrop]; simp [hsec]
    · cases hseq with
      | term htu hs1 =>
        cases hs1 with
        | nt hh1 _ hs2 =>
          cases hs2 with
          | nt hh2 _ hs3 =>
            cases hs3 with
            | nt hh3 _ hs4 =>
              cases hs4 with
              | nt hh4 _ hnil =>
                cases hnil
                have hle4 := code_step_le hok hh4
                have hle3 := code_step_le hok hh3
                have hle2 := code_step_le hok hh2
                have hle1 := code_step_le hok hh1
                obtain ⟨rfl, hdu⟩ := term_one_char (c := 0x75) rfl (by omega) hj htu
                obtain ⟨rfl, c1, hd1, hc1⟩ := hexDigit_step hok (by omega) hh1
                obtain ⟨rfl, c2, hd2, hc2⟩ := hexDigit_step hok (by omega) hh2
                obtain ⟨rfl, c3, hd3, hc3⟩ := hexDigit_step hok (by omega) hh3
                obtain ⟨rfl, c4, hd4, hc4⟩ := hexDigit_step hok hj hh4
                have hnse : isSingleEscapeCharacter natT 0x75 = false := rfl
                have hex4 : ∀ c1 c2 c3 c4 rest,
                    isHexDigit natT c1 = true → isHexDigit natT c2 = true →
                    isHexDigit natT c3 = true → isHexDigit natT c4 = true →
                    rval (escape natT (0x75 :: c1 :: c2 :: c3 :: c4 :: rest)) = some rest := by
                  intro x1 x2 x3 x4 rest hx1 hx2 hx3 hx4
                  unfold escape
                  simp [hnse, hx1, hx2, hx3, hx4]
                rw [hdu, hd1, hd2, hd3, hd4]
                exact hex4 c1 c2 c3 c4 _ hc1 hc2 hc3 hc4

private theorem stringChar_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg0 : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P)
      (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
      xs Ecma.Spec.gl cx .json .JSONStringCharacter ps i j t) :
    rval (stringCharacter natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONStringCharacter rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONStringCharacter, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
    rcases hsMem with rfl | rfl
    · cases hseq with
      | butNotN hcp hne hnil =>
        cases hnil
        cases hcp with
        | lex _ _ hl => cases hl
        | node scp hscp _ _ hseqCp =>
          rw [json_alts_rule hok cx .JSONCodePoint rfl] at hscp
          simp only [srcsOf, writtenAlts, Gen.JSON.JSONCodePoint, List.zipIdx_cons, List.zipIdx_nil,
            List.map_cons, List.map_nil, List.mem_singleton] at hscp
          subst hscp
          cases hseqCp with
          | phrase hph hnilCp =>
            cases hnilCp
            obtain ⟨c, hsc, _⟩ := hph
            have hle : i ≤ j := by have := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1; omega
            obtain ⟨rfl, _, hdrop⟩ := (slice_singleton_iff hle hj).mp hsc
            have hqF : (c == 0x22) = false := by
              rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; rintro rfl
              exact hne ⟨.t (.text "\"" false), by simp, by dsimp only [codeAlphabet]; rw [hsc]; rfl⟩
            have hbF : (c == 0x5C) = false := by
              rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; rintro rfl
              exact hne ⟨.t (.text "\\" false), by simp, by dsimp only [codeAlphabet]; rw [hsc]; rfl⟩
            have hneCtrl : isControlCharacter natT c = false := by
              rw [Bool.eq_false_iff, ne_eq]; intro hctrl
              exact hne ⟨.nt .JSONControlCharacter [], by simp, controlChar_derives hok hj hdrop hctrl⟩
            have hpredC : (!(natT.is c 0x22 || natT.is c 0x5C || isControlCharacter natT c)) = true := by
              have h1 : natT.is c 0x22 = (c == 0x22) := rfl
              have h2 : natT.is c 0x5C = (c == 0x5C) := rfl
              rw [h1, h2, hqF, hbF, hneCtrl]; rfl
            unfold stringCharacter
            rw [hdrop]; simp only [rval_or, rval_cpOf_cons, hpredC, ↓reduceIte, Option.some_or]
    · cases hseq with
      | term htb hs1 =>
        cases hs1 with
        | nt hesc _ hnil =>
          cases hnil
          obtain ⟨rfl, hdropB⟩ := term_one_char (c := 0x5C) rfl (code_step_le hok hesc) hj htb
          have hescEq := escape_step hok hj hesc
          have hpredB : (!(natT.is 0x5C 0x22 || natT.is 0x5C 0x5C || isControlCharacter natT 0x5C)) = false := rfl
          unfold stringCharacter
          rw [hdropB]; simp only [rval_or, rval_cpOf_cons, hpredB, Bool.false_eq_true, ↓reduceIte, Option.none_or]
          simp [hescEq]

private theorem stringChars_quote (cs : List Nat) :
    (stringCharacters natT (0x22 :: cs)).1 = 0x22 :: cs := by
  rw [stringCharacters.eq_1]
  have hsc : stringCharacter natT (0x22 :: cs) = none := by
    unfold stringCharacter cpOf seq cp; simp [natT]
  split
  · next r hr heq => rw [hsc] at heq; cases heq
  · rfl

private theorem stringChars_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg0 : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hq : ∃ cs, xs.drop j = 0x22 :: cs)
    (hs : Step (codeAlphabet P)
      (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
      xs Ecma.Spec.gl cx .json .JSONStringCharacters ps i j t) :
    (stringCharacters natT (xs.drop i)).1 = xs.drop j := by
  induction hsz : treeSize t using Nat.strongRecOn generalizing i j t ps with
  | ind sz ih =>
    subst hsz
    cases hs with
    | lex _ _ hl => cases hl
    | node s hsMem _ _ hseq =>
      rw [json_alts_rule hok cx .JSONStringCharacters rfl] at hsMem
      simp only [srcsOf, writtenAlts, Gen.JSON.JSONStringCharacters, List.zipIdx_cons, List.zipIdx_nil,
        List.map_cons, List.map_nil, List.mem_singleton] at hsMem
      subst hsMem
      rcases seq_nt_inv hseq with ⟨⟨⟩, _⟩ | ⟨hmid, _, _, ts', _, rfl, _, hsc, hrest⟩
      have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl; rfl) hrest
      have hscEq := stringChar_step hok (by omega) hsc
      rw [stringCharacters.eq_1]
      split
      · next r hr heq =>
        have hrEq : r = xs.drop hmid := by
          have := congrArg rval heq
          rw [hscEq, rval_some] at this
          exact Option.some.inj this.symm
        subst hrEq
        cases hrest with
        | absent hnil =>
          cases hnil
          obtain ⟨cs, hdj⟩ := hq
          dsimp only
          rw [hdj, stringChars_quote]
        | nt hscs _ hnil =>
          cases hnil
          dsimp only [treeSize, treeSize.treeListSize] at ih
          exact ih (treeSize _) (by omega) hj hq hscs rfl
      · next heq =>
        have := congrArg rval heq
        rw [hscEq, rval_none] at this; cases this

private theorem string_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg0 : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx}
    {ps : List Param} {i j : Nat} {t : Tree} (hj : j ≤ xs.length)
    (hs : Step (codeAlphabet P)
      (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
      xs Ecma.Spec.gl cx .json .JSONString ps i j t) :
    i < j ∧ xs.drop i = 0x22 :: xs.drop (i + 1) ∧
      rval (string natT (xs.drop i)) = some (xs.drop j) := by
  cases hs with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    rw [json_alts_rule hok cx .JSONString rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONString, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hsMem
    subst hsMem
    cases hseq with
    | term ht1 hrest1 =>
      have hleRest1 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hrest1
      obtain ⟨rfl, hdrop1⟩ := term_one_char (c := 0x22) rfl hleRest1 hj ht1
      cases hrest1 with
      | absent hrest2 =>
        cases hrest2 with
        | term ht2 hnil =>
          cases hnil
          obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x22) rfl (Nat.le_refl _) hj ht2
          refine ⟨by omega, hdrop1, ?_⟩
          unfold string
          rw [hdrop1]; simp only [rval_seq, rval_seqOpt, rval_cp_cons, beq_self_eq_true, ↓reduceIte,
            Option.map_some, Option.bind_some]
          rw [hdrop2, stringChars_quote]; simp
      | nt hscs _ hrest2 =>
        cases hrest2 with
        | term ht2 hnil =>
          cases hnil
          have hleScs := code_step_le hok hscs
          obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x22) rfl (Nat.le_refl _) hj ht2
          have hscsEq := stringChars_step hok (by omega) ⟨_, hdrop2⟩ hscs
          refine ⟨by omega, hdrop1, ?_⟩
          unfold string
          rw [hdrop1]; simp only [rval_seq, rval_seqOpt, rval_cp_cons, beq_self_eq_true, ↓reduceIte,
            Option.map_some, Option.bind_some]
          rw [hscsEq, hdrop2]; simp

/-! ### Non-dependent equations for `element`, `object`, `members`, `member`, `array`, `elements` -/

private theorem rval_element (l : List Nat) :
    rval (element natT l) = (rval (value natT (whiteSpace natT l).1)).map (fun r => (whiteSpace natT r).1) := by
  rw [element.eq_1]
  cases value natT (whiteSpace natT l).1 <;> rfl

private theorem rval_object_cons (c : Nat) (cs : List Nat) :
    rval (object natT (c :: cs)) =
      if !(c == 0x7B) then none
      else (rval (cp natT 0x7D (whiteSpace natT cs).1)).or
        ((rval (members natT cs)).bind (fun r => rval (cp natT 0x7D r))) := by
  rw [object.eq_1]
  have his : natT.is c 0x7B = (c == 0x7B) := rfl
  rw [his]
  split
  · rfl
  · simp only [rval_or, rval_lift, rval_optSeq]
    congr 1
    cases members natT cs with
    | none => rfl
    | some p => rcases p with ⟨r, hr⟩; simp

private theorem rval_array_cons (c : Nat) (cs : List Nat) :
    rval (array natT (c :: cs)) =
      if !(c == 0x5B) then none
      else (rval (cp natT 0x5D (whiteSpace natT cs).1)).or
        ((rval (elements natT cs)).bind (fun r => rval (cp natT 0x5D r))) := by
  rw [array.eq_1]
  have his : natT.is c 0x5B = (c == 0x5B) := rfl
  rw [his]
  split
  · rfl
  · simp only [rval_or, rval_lift, rval_optSeq]
    congr 1
    cases elements natT cs with
    | none => rfl
    | some p => rcases p with ⟨r, hr⟩; simp

private theorem rval_member (l : List Nat) :
    rval (member natT l) =
      (rval (string natT (whiteSpace natT l).1)).bind (fun ys =>
        (rval (cp natT 0x3A (whiteSpace natT ys).1)).bind (fun r => rval (element natT r))) := by
  rw [member.eq_1]
  cases h : seq (optSeq (whiteSpace natT l) (string natT)) (fun ys => optSeq (whiteSpace natT ys) (cp natT 0x3A)) with
  | none =>
    have hv : rval (seq (optSeq (whiteSpace natT l) (string natT)) (fun ys => optSeq (whiteSpace natT ys) (cp natT 0x3A))) = none := by
      rw [h]; rfl
    simp only [rval_seq, rval_optSeq] at hv
    simp only [rval_none]
    cases h1 : rval (string natT (whiteSpace natT l).1) with
    | none => rfl
    | some y => simp [h1] at hv; simp [hv]
  | some p =>
    rcases p with ⟨r, hr⟩
    have hv : rval (seq (optSeq (whiteSpace natT l) (string natT)) (fun ys => optSeq (whiteSpace natT ys) (cp natT 0x3A))) = some r := by
      rw [h]; rfl
    simp only [rval_seq, rval_optSeq] at hv
    simp only [rval_lift]
    cases h1 : rval (string natT (whiteSpace natT l).1) with
    | none => simp [h1] at hv
    | some y => simp [h1] at hv; simp [hv]

private theorem rval_members_stop {l cs : List Nat} {c : Nat}
    (hm : rval (member natT l) = some (c :: cs)) (hne : (c == 0x2C) = false) :
    rval (members natT l) = some (c :: cs) := by
  rw [members.eq_1]
  cases h : member natT l with
  | none => rw [h] at hm; cases hm
  | some p =>
    rcases p with ⟨r0, hr0⟩
    rw [h] at hm; dsimp only [rval, Option.map] at hm; injection hm with hrEq
    subst hrEq
    have his : natT.is c 0x2C = false := hne
    simp [his]

private theorem rval_members_comma {l cs r' : List Nat}
    (hm : rval (member natT l) = some (0x2C :: cs))
    (hms : rval (members natT cs) = some r') :
    rval (members natT l) = some r' := by
  rw [members.eq_1]
  cases h : member natT l with
  | none => rw [h] at hm; cases hm
  | some p =>
    rcases p with ⟨r0, hr0⟩
    rw [h] at hm; dsimp only [rval, Option.map] at hm; injection hm with hrEq
    subst hrEq
    have his : natT.is 0x2C 0x2C = true := rfl
    simp only [his, ↓reduceIte]
    cases h2 : members natT cs with
    | none => rw [h2] at hms; cases hms
    | some p2 =>
      rcases p2 with ⟨r2, hr2⟩
      rw [h2] at hms; dsimp only [rval, Option.map] at hms; exact hms

private theorem rval_elements_stop {l cs : List Nat} {c : Nat}
    (he : rval (element natT l) = some (c :: cs)) (hne : (c == 0x2C) = false) :
    rval (elements natT l) = some (c :: cs) := by
  rw [elements.eq_1]
  cases h : element natT l with
  | none => rw [h] at he; cases he
  | some p =>
    rcases p with ⟨r0, hr0⟩
    rw [h] at he; dsimp only [rval, Option.map] at he; injection he with hrEq
    subst hrEq
    have his : natT.is c 0x2C = false := hne
    simp [his]

private theorem rval_elements_comma {l cs r' : List Nat}
    (he : rval (element natT l) = some (0x2C :: cs))
    (hes : rval (elements natT cs) = some r') :
    rval (elements natT l) = some r' := by
  rw [elements.eq_1]
  cases h : element natT l with
  | none => rw [h] at he; cases he
  | some p =>
    rcases p with ⟨r0, hr0⟩
    rw [h] at he; dsimp only [rval, Option.map] at he; injection he with hrEq
    subst hrEq
    have his : natT.is 0x2C 0x2C = true := rfl
    simp only [his, ↓reduceIte]
    cases h2 : elements natT cs with
    | none => rw [h2] at hes; cases hes
    | some p2 =>
      rcases p2 with ⟨r2, hr2⟩
      rw [h2] at hes; dsimp only [rval, Option.map] at hes; exact hes

private theorem whiteSpace_advance {xs : List Nat} {a k : Nat} (hak : a ≤ k)
    (hwsp : ∀ p, a ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)
    (hstop : ∀ c cs, xs.drop k = c :: cs → isWhiteSpaceCharacter natT c = false) :
    (whiteSpace natT (xs.drop a)).1 = xs.drop k := by
  have hgen : ∀ (d p : Nat), p + d = k → a ≤ p → (whiteSpace natT (xs.drop p)).1 = xs.drop k := by
    intro d; induction d with
    | zero =>
      intro p hp _; have hpk : p = k := by omega
      subst hpk; exact whiteSpace_eq_self hstop
    | succ d ihd =>
      intro p hp hap
      obtain ⟨cw, hdcw, hwcw⟩ := hwsp p hap (by omega)
      rw [hdcw]; simp only [whiteSpace, hwcw, ↓reduceIte]
      exact ihd (p + 1) (by omega) (by omega)
  exact hgen (k - a) a (by omega) (Nat.le_refl _)

/-! ### Main mutual JSON structural completeness theorem -/

private theorem json_rec_step (hok : parseTablesOk = true) {P : CodePrims}
    {neg0 : NT → List Param → Nat → Nat → Prop} {xs : List Nat} {cx : Ctx} :
    ∀ (sz : Nat),
      -- 1: JSONElement
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length → ElemDelim (xs.drop j) →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONElement ps i j t →
        (∃ k, i ≤ k ∧ k < j ∧
          (∃ c, xs.drop k = c :: xs.drop (k + 1) ∧ isWhiteSpaceCharacter natT c = false ∧ c ≠ 0x5D) ∧
          (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
        rval (element natT (xs.drop i)) = some (xs.drop j)) ∧
      -- 2: JSONValue
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length → ValDelim (xs.drop j) →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONValue ps i j t →
        i < j ∧ (∃ c, xs.drop i = c :: xs.drop (i + 1) ∧ isWhiteSpaceCharacter natT c = false ∧ c ≠ 0x5D) ∧
          rval (value natT (xs.drop i)) = some (xs.drop j)) ∧
      -- 3: JSONObject
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONObject ps i j t →
        i < j ∧ xs.drop i = 0x7B :: xs.drop (i + 1) ∧
          rval (object natT (xs.drop i)) = some (xs.drop j)) ∧
      -- 4: JSONMembers
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length → (∃ cs, xs.drop j = 0x7D :: cs) →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONMembers ps i j t →
        (∃ k, i ≤ k ∧ k < j ∧ xs.drop k = 0x22 :: xs.drop (k + 1) ∧
          (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
        rval (members natT (xs.drop i)) = some (xs.drop j)) ∧
      -- 5: JSONMember
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length → ElemDelim (xs.drop j) →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONMember ps i j t →
        (∃ k, i ≤ k ∧ k < j ∧ xs.drop k = 0x22 :: xs.drop (k + 1) ∧
          (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
        rval (member natT (xs.drop i)) = some (xs.drop j)) ∧
      -- 6: JSONArray
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONArray ps i j t →
        i < j ∧ xs.drop i = 0x5B :: xs.drop (i + 1) ∧
          rval (array natT (xs.drop i)) = some (xs.drop j)) ∧
      -- 7: JSONElements
      (∀ {ps i j t}, treeSize t ≤ sz → j ≤ xs.length → (∃ cs, xs.drop j = 0x5D :: cs) →
        Step (codeAlphabet P)
          (fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t')
          xs Ecma.Spec.gl cx .json .JSONElements ps i j t →
        (∃ k, i ≤ k ∧ k < j ∧
          (∃ c, xs.drop k = c :: xs.drop (k + 1) ∧ isWhiteSpaceCharacter natT c = false ∧ c ≠ 0x5D) ∧
          (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
        rval (elements natT (xs.drop i)) = some (xs.drop j)) := by
  intro sz
  let neg1 := fun m ps' a b => ∃ t', Step (codeAlphabet P) neg0 xs Ecma.Spec.gl cx .json m ps' a b t'
  induction sz using Nat.strongRecOn with
  | ind sz ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- 1: JSONElement
    · intro ps i j t hsz hj hed hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONElement rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONElement, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_singleton] at hsMem
        dsimp only [treeSize] at hsz
        have hel : ∀ {k1 : Nat} {m1 : List Bool} {ts1 : List Tree},
            treeSize.treeListSize ts1 < sz → i ≤ k1 →
            (∀ p, i ≤ p → p < k1 → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true) →
            (∀ (hno1 : ∀ c cs, xs.drop k1 = c :: cs → isWhiteSpaceCharacter natT c = false),
              (whiteSpace natT (xs.drop i)).1 = xs.drop k1) →
            Seq (codeAlphabet P) neg1 xs Ecma.Spec.gl cx .json s ps 1
              [.sym (.nt .JSONValue []) false, .sym (.nt .JSONWhiteSpace []) true] k1 j m1 ts1 →
            (∃ k, i ≤ k ∧ k < j ∧
              (∃ c, xs.drop k = c :: xs.drop (k + 1) ∧ isWhiteSpaceCharacter natT c = false ∧ c ≠ 0x5D) ∧
              (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
            rval (element natT (xs.drop i)) = some (xs.drop j) := by
          intro k1 m1 ts1 hts1 hik1 hwsp1 hws1 hseq1
          rcases seq_nt_inv hseq1 with ⟨⟨⟩, _⟩ | ⟨k2, _, _, _, _, rfl, _, hval, hseq2⟩
          dsimp only [treeSize.treeListSize] at hts1
          have hle2 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl; rfl) hseq2
          cases hseq2 with
          | absent hnil =>
            cases hnil
            obtain ⟨hltV, ⟨cv, hdV, hnwV, hne5d⟩, hvalEq⟩ :=
              (ih (treeSize _) (by omega)).2.1 (Nat.le_refl _) hj (elemDelim_valDelim hed) hval
            have hws1Eq := hws1 (by intro c cs hr; rw [hdV] at hr; cases hr; exact hnwV)
            have hws2Eq := whiteSpace_eq_self (elemDelim_not_ws hed)
            refine ⟨⟨k1, hik1, hltV, ⟨cv, hdV, hnwV, hne5d⟩, hwsp1⟩, ?_⟩
            rw [rval_element, hws1Eq, hvalEq]; simp [hws2Eq]
          | nt hws2 _ hnil =>
            cases hnil
            obtain ⟨hltWs2, ⟨cw2, hdw2, hwc2⟩, hws2Eq⟩ :=
              whiteSpace_step hok hj (elemDelim_not_ws hed) hws2
            have hvd2 : ValDelim (xs.drop k2) := by
              intro c cs hr; rw [hdw2] at hr; cases hr
              unfold isWhiteSpaceCharacter natT at hwc2
              simp only [Bool.or_eq_true, beq_iff_eq] at hwc2
              rcases hwc2 with ((h | h) | h) | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
            obtain ⟨hltV, ⟨cv, hdV, hnwV, hne5d⟩, hvalEq⟩ :=
              (ih (treeSize _) (by omega)).2.1 (Nat.le_refl _) (by omega) hvd2 hval
            have hws1Eq := hws1 (by intro c cs hr; rw [hdV] at hr; cases hr; exact hnwV)
            refine ⟨⟨k1, hik1, by omega, ⟨cv, hdV, hnwV, hne5d⟩, hwsp1⟩, ?_⟩
            rw [rval_element, hws1Eq, hvalEq]; simp [hws2Eq]
        subst hsMem
        cases hseq with
        | absent hseq1 =>
          exact hel (by omega) (Nat.le_refl _) (fun _ hip hltp => by omega) (fun hno1 => whiteSpace_eq_self hno1) hseq1
        | nt hws1 _ hseq1 =>
          dsimp only [treeSize.treeListSize] at hsz
          have hle1 := code_step_le hok hws1
          have hleRest := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hseq1
          exact hel (by omega) hle1 (whiteSpace_chars hok (by omega) hws1)
            (fun hno1 => (whiteSpace_step hok (by omega) hno1 hws1).2.2) hseq1
    -- 2: JSONValue
    · intro ps i j t hsz hj hvd hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONValue rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONValue, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
        dsimp only [treeSize] at hsz
        rcases hsMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · -- JSONObject
          cases hseq with
          | nt hobj _ hnil =>
            cases hnil; dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨hlt, hd, hobjEq⟩ := (ih (treeSize _) (by omega)).2.2.1 (Nat.le_refl _) hj hobj
            refine ⟨hlt, ⟨0x7B, hd, by decide, by decide⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hobjEq]; rfl
        · -- JSONArray
          cases hseq with
          | nt harr _ hnil =>
            cases hnil; dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨hlt, hd, harrEq⟩ := (ih (treeSize _) (by omega)).2.2.2.2.2.1 (Nat.le_refl _) hj harr
            have hnoObj : rval (object natT (xs.drop i)) = none := by rw [hd, rval_object_cons]; rfl
            refine ⟨hlt, ⟨0x5B, hd, by decide, by decide⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hnoObj, harrEq]; rfl
        · -- JSONNumber
          cases hseq with
          | nt hnum _ hnil =>
            cases hnil
            obtain ⟨hlt, ⟨c, hd, hnumC⟩, hnumEq⟩ := number_step hok hj hvd hnum
            have hnw : isWhiteSpaceCharacter natT c = false := by
              rcases hnumC with rfl | hdc
              · decide
              · rw [isDigit, inRange_natT] at hdc; have := of_decide_eq_true hdc
                unfold isWhiteSpaceCharacter natT; simp; omega
            have hne5d : c ≠ 0x5D := by
              rcases hnumC with rfl | hdc
              · decide
              · rw [isDigit, inRange_natT] at hdc; have := of_decide_eq_true hdc; omega
            have hneObj : (c == 0x7B) = false := by
              rcases hnumC with rfl | hdc
              · decide
              · rw [isDigit, inRange_natT] at hdc; have := of_decide_eq_true hdc
                rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; omega
            have hneArr : (c == 0x5B) = false := by
              rcases hnumC with rfl | hdc
              · decide
              · rw [isDigit, inRange_natT] at hdc; have := of_decide_eq_true hdc
                rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; omega
            have hnoObj : rval (object natT (xs.drop i)) = none := by rw [hd, rval_object_cons, hneObj]; rfl
            have hnoArr : rval (array natT (xs.drop i)) = none := by rw [hd, rval_array_cons, hneArr]; rfl
            refine ⟨hlt, ⟨c, hd, hnw, hne5d⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hnoObj, hnoArr, hnumEq]; rfl
        · -- JSONString
          cases hseq with
          | nt hstr _ hnil =>
            cases hnil
            obtain ⟨hlt, hd, hstrEq⟩ := string_step hok hj hstr
            have hnoObj : rval (object natT (xs.drop i)) = none := by rw [hd, rval_object_cons]; rfl
            have hnoArr : rval (array natT (xs.drop i)) = none := by rw [hd, rval_array_cons]; rfl
            have hnoNum : rval (number natT (xs.drop i)) = none := by
              rw [hd]; exact rval_number_none_of_char rfl rfl rfl
            refine ⟨hlt, ⟨0x22, hd, rfl, by decide⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hnoObj, hnoArr, hnoNum, hstrEq]; rfl
        · -- "true"
          cases hseq with
          | term ht hnil =>
            cases hnil
            dsimp only [codeAlphabet] at ht
            have hsc : slice xs i j = [0x74, 0x72, 0x75, 0x65] := ht
            have hle : i ≤ j := by have := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1; omega
            obtain ⟨hlen, hdrop⟩ := (slice_eq_iff_drop hle hj).mp hsc
            have hjEq : j = i + 4 := by simp at hlen; omega
            subst hjEq
            have hd1 : xs.drop i = 0x74 :: xs.drop (i + 1) := by
              have h1 : slice xs i (i + 1) = [0x74] := by
                unfold slice; rw [hdrop, show (i + 1) - i = 1 from by omega]; rfl
              exact ((slice_singleton_iff (by omega) (by omega)).mp h1).2.2
            have hnoObj : rval (object natT (xs.drop i)) = none := by rw [hd1, rval_object_cons]; rfl
            have hnoArr : rval (array natT (xs.drop i)) = none := by rw [hd1, rval_array_cons]; rfl
            have hnoNum : rval (number natT (xs.drop i)) = none := by
              rw [hd1]; exact rval_number_none_of_char rfl rfl rfl
            have hnoStr : rval (string natT (xs.drop i)) = none := by unfold string; rw [hd1]; simp
            have hcps := rval_cps_exact [0x74, 0x72, 0x75, 0x65] (xs.drop (i + 4)) (by decide)
            refine ⟨by omega, ⟨0x74, hd1, rfl, by decide⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hnoObj, hnoArr, hnoNum, hnoStr]
            rw [hdrop, hcps]; rfl
        · -- "false"
          cases hseq with
          | term ht hnil =>
            cases hnil
            dsimp only [codeAlphabet] at ht
            have hsc : slice xs i j = [0x66, 0x61, 0x6C, 0x73, 0x65] := ht
            have hle : i ≤ j := by have := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1; omega
            obtain ⟨hlen, hdrop⟩ := (slice_eq_iff_drop hle hj).mp hsc
            have hjEq : j = i + 5 := by simp at hlen; omega
            subst hjEq
            have hd1 : xs.drop i = 0x66 :: xs.drop (i + 1) := by
              have h1 : slice xs i (i + 1) = [0x66] := by
                unfold slice; rw [hdrop, show (i + 1) - i = 1 from by omega]; rfl
              exact ((slice_singleton_iff (by omega) (by omega)).mp h1).2.2
            have hnoObj : rval (object natT (xs.drop i)) = none := by rw [hd1, rval_object_cons]; rfl
            have hnoArr : rval (array natT (xs.drop i)) = none := by rw [hd1, rval_array_cons]; rfl
            have hnoNum : rval (number natT (xs.drop i)) = none := by
              rw [hd1]; exact rval_number_none_of_char rfl rfl rfl
            have hnoStr : rval (string natT (xs.drop i)) = none := by unfold string; rw [hd1]; simp
            have hnoTrue : rval (cps natT [0x74, 0x72, 0x75, 0x65] (xs.drop i)) = none := by rw [hd1]; rfl
            have hcps := rval_cps_exact [0x66, 0x61, 0x6C, 0x73, 0x65] (xs.drop (i + 5)) (by decide)
            refine ⟨by omega, ⟨0x66, hd1, rfl, by decide⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hnoObj, hnoArr, hnoNum, hnoStr, hnoTrue]
            rw [hdrop, hcps]; rfl
        · -- "null"
          cases hseq with
          | term ht hnil =>
            cases hnil
            dsimp only [codeAlphabet] at ht
            have hsc : slice xs i j = [0x6E, 0x75, 0x6C, 0x6C] := ht
            have hle : i ≤ j := by have := (slice_nonempty_lt (by rw [hsc]; exact List.cons_ne_nil _ _)).1; omega
            obtain ⟨hlen, hdrop⟩ := (slice_eq_iff_drop hle hj).mp hsc
            have hjEq : j = i + 4 := by simp at hlen; omega
            subst hjEq
            have hd1 : xs.drop i = 0x6E :: xs.drop (i + 1) := by
              have h1 : slice xs i (i + 1) = [0x6E] := by
                unfold slice; rw [hdrop, show (i + 1) - i = 1 from by omega]; rfl
              exact ((slice_singleton_iff (by omega) (by omega)).mp h1).2.2
            have hnoObj : rval (object natT (xs.drop i)) = none := by rw [hd1, rval_object_cons]; rfl
            have hnoArr : rval (array natT (xs.drop i)) = none := by rw [hd1, rval_array_cons]; rfl
            have hnoNum : rval (number natT (xs.drop i)) = none := by
              rw [hd1]; exact rval_number_none_of_char rfl rfl rfl
            have hnoStr : rval (string natT (xs.drop i)) = none := by unfold string; rw [hd1]; simp
            have hnoTrue : rval (cps natT [0x74, 0x72, 0x75, 0x65] (xs.drop i)) = none := by rw [hd1]; rfl
            have hnoFalse : rval (cps natT [0x66, 0x61, 0x6C, 0x73, 0x65] (xs.drop i)) = none := by rw [hd1]; rfl
            have hcps := rval_cps_exact [0x6E, 0x75, 0x6C, 0x6C] (xs.drop (i + 4)) (by decide)
            refine ⟨by omega, ⟨0x6E, hd1, rfl, by decide⟩, ?_⟩
            rw [value.eq_1]; simp only [rval_or, hnoObj, hnoArr, hnoNum, hnoStr, hnoTrue, hnoFalse]
            rw [hdrop, hcps]; rfl
    -- 3: JSONObject
    · intro ps i j t hsz hj hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONObject rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONObject, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
        dsimp only [treeSize] at hsz
        rcases hsMem with rfl | rfl
        · -- '{' ws? '}'
          cases hseq with
          | term ht1 hrest1 =>
            have hleRest1 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hrest1
            obtain ⟨rfl, hdrop1⟩ := term_one_char (c := 0x7B) rfl hleRest1 hj ht1
            cases hrest1 with
            | absent hrest2 =>
              cases hrest2 with
              | term ht2 hnil =>
                cases hnil
                obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x7D) rfl (Nat.le_refl _) hj ht2
                have hwsEq : (whiteSpace natT (xs.drop (i + 1))).1 = 0x7D :: xs.drop (i + 1 + 1) := by
                  rw [hdrop2]; exact whiteSpace_eq_self (by intro c cs hr; cases hr; rfl)
                refine ⟨by omega, hdrop1, ?_⟩
                rw [hdrop1, rval_object_cons, hwsEq]; simp
            | nt hws _ hrest2 =>
              cases hrest2 with
              | term ht2 hnil =>
                cases hnil
                have hleWs := code_step_le hok hws
                obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x7D) rfl (Nat.le_refl _) hj ht2
                obtain ⟨_, _, hwsEq⟩ := whiteSpace_step hok (by omega)
                  (by intro c cs hr; rw [hdrop2] at hr; cases hr; rfl) hws
                refine ⟨by omega, hdrop1, ?_⟩
                rw [hdrop1, rval_object_cons, hwsEq, hdrop2]; simp
        · -- '{' JSONMembers '}'
          cases hseq with
          | term ht1 hrest1 =>
            cases hrest1 with
            | nt hmems _ hrest2 =>
              cases hrest2 with
              | term ht2 hnil =>
                cases hnil
                dsimp only [treeSize.treeListSize, treeSize] at hsz
                have hleMems := code_step_le hok hmems
                obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x7D) rfl (Nat.le_refl _) hj ht2
                obtain ⟨rfl, hdrop1⟩ := term_one_char (c := 0x7B) rfl (by omega) hj ht1
                obtain ⟨⟨kq, hkq1, hkq2, hdkq, hwsp⟩, hmemsEq⟩ :=
                  (ih (treeSize _) (by omega)).2.2.2.1 (Nat.le_refl _) (by omega) ⟨_, hdrop2⟩ hmems
                have hwsStop := whiteSpace_advance hkq1 hwsp
                  (by intro c cs hr; rw [hdkq] at hr; cases hr; rfl)
                refine ⟨by omega, hdrop1, ?_⟩
                rw [hdrop1, rval_object_cons, hwsStop, hdkq, hmemsEq, hdrop2]; simp
    -- 4: JSONMembers
    · intro ps i j t hsz hj hbrace hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONMembers rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONMembers, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
        dsimp only [treeSize] at hsz
        rcases hsMem with rfl | rfl
        · cases hseq with
          | nt hmem _ hnil =>
            cases hnil; dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨cs, hdj⟩ := hbrace
            have hed : ElemDelim (xs.drop j) := by
              intro c cs' hr; rw [hdj] at hr; cases hr; exact Or.inr (Or.inl rfl)
            obtain ⟨hlead, hmemEq⟩ := (ih (treeSize _) (by omega)).2.2.2.2.1 (Nat.le_refl _) hj hed hmem
            refine ⟨hlead, ?_⟩
            rw [hdj] at hmemEq ⊢
            exact rval_members_stop hmemEq rfl
        · rcases seq_nt_inv hseq with ⟨⟨⟩, _⟩ | ⟨km, _, _, _, _, rfl, _, hmem, hrest1⟩
          cases hrest1 with
          | term htc hrest2 =>
            cases hrest2 with
            | nt hmems _ hnil =>
              cases hnil
              dsimp only [treeSize.treeListSize, treeSize] at hsz
              have hleMem := code_step_le hok hmem
              have hleMems := code_step_le hok hmems
              obtain ⟨rfl, hdropC⟩ := term_one_char (c := 0x2C) rfl hleMems hj htc
              have hed1 : ElemDelim (xs.drop km) := by
                intro c cs' hr; rw [hdropC] at hr; cases hr; exact Or.inl rfl
              obtain ⟨⟨kq, hkq1, hkq2, hdkq, hwsp⟩, hmemEq⟩ :=
                (ih (treeSize _) (by omega)).2.2.2.2.1 (Nat.le_refl _) (by omega) hed1 hmem
              obtain ⟨_, hmemsEq⟩ :=
                (ih (treeSize _) (by omega)).2.2.2.1 (Nat.le_refl _) hj hbrace hmems
              refine ⟨⟨kq, hkq1, by omega, hdkq, hwsp⟩, ?_⟩
              rw [hdropC] at hmemEq
              exact rval_members_comma hmemEq hmemsEq
    -- 5: JSONMember
    · intro ps i j t hsz hj hed hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONMember rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONMember, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_singleton] at hsMem
        dsimp only [treeSize] at hsz
        have hmb : ∀ {k1 : Nat} {m1 : List Bool} {ts1 : List Tree},
            treeSize.treeListSize ts1 < sz → i ≤ k1 →
            (∀ p, i ≤ p → p < k1 → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true) →
            (∀ (hno1 : ∀ c cs, xs.drop k1 = c :: cs → isWhiteSpaceCharacter natT c = false),
              (whiteSpace natT (xs.drop i)).1 = xs.drop k1) →
            Seq (codeAlphabet P) neg1 xs Ecma.Spec.gl cx .json s ps 1
              [.sym (.nt .JSONString []) false, .sym (.nt .JSONWhiteSpace []) true,
               .sym (.t (.text ":" false)) false, .sym (.nt .JSONElement []) false] k1 j m1 ts1 →
            (∃ k, i ≤ k ∧ k < j ∧ xs.drop k = 0x22 :: xs.drop (k + 1) ∧
              (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
            rval (member natT (xs.drop i)) = some (xs.drop j) := by
          intro k1 m1 ts1 hts1 hik1 hwsp1 hws1 hseq1
          cases hseq1 with
          | nt hstr _ hseq2 =>
            dsimp only [treeSize.treeListSize] at hts1
            have hleSeq2 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl | rfl <;> rfl) hseq2
            obtain ⟨hltStr, hdStr, hstrEq⟩ := string_step hok (by omega) hstr
            have hws1Eq := hws1 (by intro c cs hr; rw [hdStr] at hr; cases hr; rfl)
            have hmb2 : ∀ {k2 k3 : Nat} {m3 : List Bool} {ts3 : List Tree},
                rval (string natT (xs.drop k1)) = some (xs.drop k2) →
                treeSize.treeListSize ts3 < sz → k2 ≤ k3 →
                (∀ (hno2 : ∀ c cs, xs.drop k3 = c :: cs → isWhiteSpaceCharacter natT c = false),
                  (whiteSpace natT (xs.drop k2)).1 = xs.drop k3) →
                Seq (codeAlphabet P) neg1 xs Ecma.Spec.gl cx .json s ps 3
                  [.sym (.t (.text ":" false)) false, .sym (.nt .JSONElement []) false] k3 j m3 ts3 →
                (∃ k, i ≤ k ∧ k < j ∧ xs.drop k = 0x22 :: xs.drop (k + 1) ∧
                  (∀ p, i ≤ p → p < k → ∃ c, xs.drop p = c :: xs.drop (p + 1) ∧ isWhiteSpaceCharacter natT c = true)) ∧
                rval (member natT (xs.drop i)) = some (xs.drop j) := by
              intro k2 k3 m3 ts3 hstrEq2 hts3 hk23 hws2 hseq3
              cases hseq3 with
              | term htc hseq4 =>
                cases hseq4 with
                | nt hel _ hnil =>
                  cases hnil
                  dsimp only [treeSize.treeListSize, treeSize] at hts3
                  have hleEl := code_step_le hok hel
                  obtain ⟨rfl, hdropC⟩ := term_one_char (c := 0x3A) rfl hleEl hj htc
                  have hws2Eq := hws2 (by intro c cs hr; rw [hdropC] at hr; cases hr; rfl)
                  obtain ⟨_, helEq⟩ := (ih (treeSize _) (by omega)).1 (Nat.le_refl _) hj hed hel
                  refine ⟨⟨k1, hik1, by omega, hdStr, hwsp1⟩, ?_⟩
                  rw [rval_member, hws1Eq, hstrEq2]; simp only [Option.bind_some]
                  rw [hws2Eq, hdropC]; simp [helEq]
            cases hseq2 with
            | absent hseq3 =>
              exact hmb2 hstrEq (by omega) (Nat.le_refl _) (fun hno2 => whiteSpace_eq_self hno2) hseq3
            | nt hws2 _ hseq3 =>
              dsimp only [treeSize.treeListSize] at hts1
              have hleWs2 := code_step_le hok hws2
              have hleSeq3 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hseq3
              exact hmb2 hstrEq (by omega) hleWs2 (fun hno2 => (whiteSpace_step hok (by omega) hno2 hws2).2.2) hseq3
        subst hsMem
        cases hseq with
        | absent hseq1 =>
          exact hmb (by omega) (Nat.le_refl _) (fun _ hip hltp => by omega) (fun hno1 => whiteSpace_eq_self hno1) hseq1
        | nt hws1 _ hseq1 =>
          dsimp only [treeSize.treeListSize] at hsz
          have hleWs1 := code_step_le hok hws1
          have hleSeq1 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl | rfl | rfl <;> rfl) hseq1
          exact hmb (by omega) hleWs1 (whiteSpace_chars hok (by omega) hws1)
            (fun hno1 => (whiteSpace_step hok (by omega) hno1 hws1).2.2) hseq1
    -- 6: JSONArray
    · intro ps i j t hsz hj hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONArray rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONArray, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
        dsimp only [treeSize] at hsz
        rcases hsMem with rfl | rfl
        · -- '[' ws? ']'
          cases hseq with
          | term ht1 hrest1 =>
            have hleRest1 := code_seq_le hok (by intro it hit; simp at hit; rcases hit with rfl | rfl <;> rfl) hrest1
            obtain ⟨rfl, hdrop1⟩ := term_one_char (c := 0x5B) rfl hleRest1 hj ht1
            cases hrest1 with
            | absent hrest2 =>
              cases hrest2 with
              | term ht2 hnil =>
                cases hnil
                obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x5D) rfl (Nat.le_refl _) hj ht2
                have hwsEq : (whiteSpace natT (xs.drop (i + 1))).1 = 0x5D :: xs.drop (i + 1 + 1) := by
                  rw [hdrop2]; exact whiteSpace_eq_self (by intro c cs hr; cases hr; rfl)
                refine ⟨by omega, hdrop1, ?_⟩
                rw [hdrop1, rval_array_cons, hwsEq]; simp
            | nt hws _ hrest2 =>
              cases hrest2 with
              | term ht2 hnil =>
                cases hnil
                have hleWs := code_step_le hok hws
                obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x5D) rfl (Nat.le_refl _) hj ht2
                obtain ⟨_, _, hwsEq⟩ := whiteSpace_step hok (by omega)
                  (by intro c cs hr; rw [hdrop2] at hr; cases hr; rfl) hws
                refine ⟨by omega, hdrop1, ?_⟩
                rw [hdrop1, rval_array_cons, hwsEq, hdrop2]; simp
        · -- '[' JSONElements ']'
          cases hseq with
          | term ht1 hrest1 =>
            cases hrest1 with
            | nt hels _ hrest2 =>
              cases hrest2 with
              | term ht2 hnil =>
                cases hnil
                dsimp only [treeSize.treeListSize, treeSize] at hsz
                have hleEls := code_step_le hok hels
                obtain ⟨rfl, hdrop2⟩ := term_one_char (c := 0x5D) rfl (Nat.le_refl _) hj ht2
                obtain ⟨rfl, hdrop1⟩ := term_one_char (c := 0x5B) rfl (by omega) hj ht1
                obtain ⟨⟨kv, hkv1, hkv2, ⟨cv, hdcv, hnwcv, hne5d⟩, hwsp⟩, helsEq⟩ :=
                  (ih (treeSize _) (by omega)).2.2.2.2.2.2 (Nat.le_refl _) (by omega) ⟨_, hdrop2⟩ hels
                have hwsStop := whiteSpace_advance (xs := xs) hkv1 hwsp
                  (by intro c cs hr; rw [hdcv] at hr; cases hr; exact hnwcv)
                have hneB : (cv == 0x5D) = false := by rw [Bool.eq_false_iff, ne_eq, beq_iff_eq]; exact hne5d
                refine ⟨by omega, hdrop1, ?_⟩
                rw [hdrop1, rval_array_cons, hwsStop, hdcv, helsEq, hdrop2]; simp [hneB]
    -- 7: JSONElements
    · intro ps i j t hsz hj hbrack hs
      cases hs with
      | lex _ _ hl => cases hl
      | node s hsMem _ _ hseq =>
        rw [json_alts_rule hok cx .JSONElements rfl] at hsMem
        simp only [srcsOf, writtenAlts, Gen.JSON.JSONElements, List.zipIdx_cons, List.zipIdx_nil,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hsMem
        dsimp only [treeSize] at hsz
        rcases hsMem with rfl | rfl
        · cases hseq with
          | nt hel _ hnil =>
            cases hnil; dsimp only [treeSize.treeListSize] at hsz
            obtain ⟨cs, hdj⟩ := hbrack
            have hed : ElemDelim (xs.drop j) := by
              intro c cs' hr; rw [hdj] at hr; cases hr; exact Or.inr (Or.inr rfl)
            obtain ⟨hlead, helEq⟩ := (ih (treeSize _) (by omega)).1 (Nat.le_refl _) hj hed hel
            refine ⟨hlead, ?_⟩
            rw [hdj] at helEq ⊢
            exact rval_elements_stop helEq rfl
        · rcases seq_nt_inv hseq with ⟨⟨⟩, _⟩ | ⟨ke, _, _, _, _, rfl, _, hel, hrest1⟩
          cases hrest1 with
          | term htc hrest2 =>
            cases hrest2 with
            | nt hels _ hnil =>
              cases hnil
              dsimp only [treeSize.treeListSize, treeSize] at hsz
              have hleEl := code_step_le hok hel
              have hleEls := code_step_le hok hels
              obtain ⟨rfl, hdropC⟩ := term_one_char (c := 0x2C) rfl hleEls hj htc
              have hed1 : ElemDelim (xs.drop ke) := by
                intro c cs' hr; rw [hdropC] at hr; cases hr; exact Or.inl rfl
              obtain ⟨⟨kv, hkv1, hkv2, hcv, hwsp⟩, helEq⟩ :=
                (ih (treeSize _) (by omega)).1 (Nat.le_refl _) (by omega) hed1 hel
              obtain ⟨_, helsEq⟩ :=
                (ih (treeSize _) (by omega)).2.2.2.2.2.2 (Nat.le_refl _) hj hbrack hels
              refine ⟨⟨kv, hkv1, by omega, hcv, hwsp⟩, ?_⟩
              rw [hdropC] at helEq
              exact rval_elements_comma helEq helsEq

end JsonProof

/-- Completeness of `Engine.JsonText.text`: every derivation of `JSONText` over `xs` in `.json`
is accepted by `Engine.JsonText.text`. -/
theorem jsonText_complete (hok : parseTablesOk = true)
    {cx : Ctx} {P : CodePrims} {xs : List Nat} {ps : List Param} {t : Tree}
    (hd : Derives Ecma.Spec.gl cx .json (codeAlphabet P) xs .JSONText ps 0 xs.length t) :
    Engine.JsonText.text ⟨(· == ·), (· < ·)⟩ xs = true := by
  obtain ⟨K, hK⟩ := hd
  have hstep := hK (max K 2) (Nat.le_max_left K 2)
  have hk2 : ∃ k0, max K 2 = k0 + 2 := ⟨max K 2 - 2, by omega⟩
  obtain ⟨k0, hk0⟩ := hk2
  rw [hk0] at hstep
  dsimp only [DerivesAt] at hstep
  generalize hi0 : (0 : Nat) = i0 at hstep
  generalize hj0 : xs.length = j0 at hstep
  cases hstep with
  | lex _ _ hl => cases hl
  | node s hsMem _ _ hseq =>
    subst hi0; subst hj0
    rw [JsonProof.json_alts_rule hok cx .JSONText rfl] at hsMem
    simp only [srcsOf, writtenAlts, Gen.JSON.JSONText, List.zipIdx_cons, List.zipIdx_nil,
      List.map_cons, List.map_nil, List.mem_singleton] at hsMem
    subst hsMem
    cases hseq with
    | nt hel _ hnil =>
      cases hnil
      have hed : JsonProof.ElemDelim (xs.drop xs.length) := by
        rw [List.drop_length]; intro _ _ h; cases h
      obtain ⟨_, helEq⟩ :=
        (JsonProof.json_rec_step hok (treeSize _)).1 (Nat.le_refl _) (Nat.le_refl _) hed hel
      simp only [List.drop_length] at helEq
      have hel0 : JsonProof.rval (Engine.JsonText.element JsonProof.natT xs) = some [] := helEq
      change Engine.JsonText.text JsonProof.natT xs = true
      unfold Engine.JsonText.text
      cases h : Engine.JsonText.element JsonProof.natT xs with
      | none => rw [h] at hel0; cases hel0
      | some p =>
        rcases p with ⟨r, hr⟩
        rw [h] at hel0
        dsimp only [JsonProof.rval, Option.map] at hel0
        injection hel0 with hr0
        subst hr0
        rfl

/-- Completeness of `Engine.noJSON`: when `Engine.noJSON goal cs = true`, no grammar in
`GrammarCtx.Parses` derives `(goal, ps)` over `cs.toList`. -/
theorem noJSON_complete (hok : parseTablesOk = true)
    {cx : Ctx} {P : CodePrims} {strict : Bool} {goal : NT} {ps : List Param} {cs : Array Nat}
    (hno : Engine.noJSON goal.ctorIdx cs = true) :
    ∀ t, ¬ ({ gl := Ecma.Spec.gl, cx := cx, P := P, strict := strict } : Ecma.GrammarCtx).Parses goal ps cs.toList t := by
  unfold Engine.noJSON at hno
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hno
  obtain ⟨hgoalIdx, htextF⟩ := hno
  have hgoal : goal = .JSONText := nt_ctorIdx_inj hgoalIdx
  subst hgoal
  obtain ⟨_, _, hrSyn, hrJson, _, _, hordJson, _⟩ := fast_invariants hok cx
  intro t hp
  unfold Ecma.GrammarCtx.Parses at hp
  have hnoSyn : (Ecma.Spec.gl.rulesOf .syntactic).any (·.lhs == .JSONText) = false := by
    rw [Bool.eq_false_iff, ne_eq]; intro h
    have := ruleNt_of_rulesOf hok h
    rw [hrSyn] at this; cases this
  simp only [hnoSyn, Bool.false_eq_true, ↓reduceIte] at hp
  obtain ⟨g, hgMem, hgRule, hpCode⟩ := hp
  have hgEq : g = .json := by
    have h1 := ruleNt_of_rulesOf hok hgRule
    have hmem : (g, NT.JSONText) ∈ codeGrammars.filterMap (fun g' => (ruleNt g' NT.JSONText.ctorIdx).map ((g', ·))) := by
      rw [List.mem_filterMap]
      exact ⟨g, hgMem, by rw [h1]; rfl⟩
    rw [hrJson, List.mem_singleton] at hmem
    injection hmem
  subst hgEq
  unfold ParsesCode at hpCode
  rw [← orderedBy_eq hok cx .json, hordJson] at hpCode
  simp only [Bool.false_eq_true, ↓reduceIte] at hpCode
  have htrue := jsonText_complete hok hpCode
  rw [htrue] at htextF
  cases htextF

end Engine.Parse
