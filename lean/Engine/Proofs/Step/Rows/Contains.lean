module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.ProgEq

@[expose] public section

/-!
# The step claim: Contains' and ComputedPropertyContains' rows (the first SDO rows)

`SdoRowOk X s e`: what an SDO's row of the table owes (`Sound.sdo` at that SDO). `contains_sdoRow`: the walk
`Engine.Accel.Contains.accelSdo` at SDOs 23 and 24 meets it, given `containsRowsCheck = true`, a Boolean check of
the program's row table (checked at runtime in `Engine.Pins`).

* The walk's answer at a Parse Node is the machine's steps from the call to the Boolean, in the same state and
  frames (`ContainsRec`), by induction on the walk's depth (`contains_walk`): the call enters the row's code in a
  frame under the scope of the Parse Nodes being evaluated (`contains_at_row`), or Contains' default definition
  (`contains_at_dflt`), or defers along a chain production (`contains_at_chain`); the scope is undone as the value
  returns (`contains_scope_ret`).
* A row's code is one of eleven (`containsShapes`), each with its steps: `contains_ret_steps`,
  `contains_any1_steps`, `contains_isSym_steps`, `contains_super_steps`, `contains_arrow2_steps`,
  `contains_arrow1_steps`, `contains_arrowDecl_steps`, `contains_classTail_steps`, `contains_cpc1_steps`,
  `contains_cpcPh_steps`, `contains_cpc2_steps`.
* The default definition's loop over the children is an induction on the walk's fuel (`contains_dflt_loop`):
  `contains_read_true`, `contains_read_false`.
* `ContainsRows` is what the walk needs of the program's rows at every production; `containsRows_of_check` gives
  it from the check, through `contains_row_key`: a production with a row is a key of the source's row table.
-/

namespace Engine.Machine

open Ecma Ecma.Machine
open Engine.Accel

set_option maxRecDepth 8000 in
theorem contains_rc23 : Engine.P.sdoRc Known.sdoContains = false := by
  unfold Engine.P
  dsimp only [Prog.memo, Src.expanded, Src.prog, Src.index]
  rfl

set_option maxRecDepth 8000 in
theorem contains_rc24 : Engine.P.sdoRc Known.sdoComputedPropertyContains = false := by
  unfold Engine.P
  dsimp only [Prog.memo, Src.expanded, Src.prog, Src.index]
  rfl

set_option maxRecDepth 8000 in
theorem contains_arity23 : Engine.P.sdoArity Known.sdoContains = 1 := by
  unfold Engine.P
  dsimp only [Prog.memo, Src.expanded, Src.prog, Src.index]
  rfl

set_option maxRecDepth 8000 in
theorem contains_arity24 : Engine.P.sdoArity Known.sdoComputedPropertyContains = 1 := by
  unfold Engine.P
  dsimp only [Prog.memo, Src.expanded, Src.prog, Src.index]
  rfl

set_option maxRecDepth 8000 in
theorem contains_sort56 : Engine.P.sortDef Known.sNonterminal = some { super := [Known.sGrammarSymbol], test := .prim Known.pIsNonterminal [.subject] false, record := false } := by
  rw [sortDef_eq]; rfl

/-- `gstep`, but not at an SDO's call either. -/
macro "cstep" : tactic => `(tactic| (
  fail_if_success (show Steps _ ⟨_, _, .invoke (.sdo _ _ _)⟩ _)
  gstep))

macro "csteps" : tactic => `(tactic| repeat cstep)

/-- Transitions up to the configuration aimed at. -/
macro "csteps_to" : tactic => `(tactic| repeat (first | exact Steps.refl _ | cstep))

/-- Transitions up to the read of the symbol (slot 0). -/
macro "csteps_var" : tactic => `(tactic| repeat (
  fail_if_success (show Steps _ ⟨_, _, .op (.var 0)⟩ _)
  cstep))

theorem contains_symOf {v : Val F} {sym : Contains.Sym} (h : Contains.symOf v = some sym) :
    (∃ k, v = .nt k [] ∧ sym = .nt k) ∨ (∃ t, v = .term t ∧ sym = .term t) := by
  unfold Contains.symOf at h
  split at h
  · cases h; exact .inl ⟨_, rfl, rfl⟩
  · cases h; exact .inr ⟨_, rfl, rfl⟩
  · cases h

/-- The nested calls' answers are the machine's: what the walk's induction gives a row. -/
def ContainsRec (X : Ctx F) (v : Val F) (rec : SdoId → F.Node → Option Bool) : Prop :=
  ∀ (s' : SdoId) (ch : F.Node) (b : Bool), rec s' ch = some b → ∀ (st : State F) (fr : List (Frame F)),
    Steps X ⟨st, fr, .invoke (.sdo s' ch [v])⟩ ⟨st, fr, .val (.bool b)⟩

theorem contains_ret_steps (X : Ctx F) (s : State F) (fs : List (Frame F)) (a : AlgId) (nd : F.Node)
    (sl : Array (Val F)) :
    Steps X ⟨s, ⟨a, some nd, sl, .steps false true false, [], [], none⟩ :: fs, .code containsRetCode⟩
      ⟨s, fs, .val (.bool false)⟩ := by
  csteps
  exact .refl _


/-- ph-result-of's steps: its argument. -/
theorem contains_res_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (b : Bool) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨Known.cPhResultOf, 0⟩ [.bool b])⟩ ⟨s, fr, .val (.bool b)⟩ := by
  refine Steps.next (step_alg H chk s fr _ _ containsResAlg containsResCode containsResAlg_pin containsResCode_pin) ?_
  csteps
  exact .refl _

/-- ph-contains' steps: Contains of the node. -/
theorem contains_ph_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (ch : F.Node) (b : Bool)
    (hrec : ∀ (st : State F) (fr : List (Frame F)),
      Steps (Ctx.spec Engine.P' H chk) ⟨st, fr, .invoke (.sdo Known.sdoContains ch [v])⟩ ⟨st, fr, .val (.bool b)⟩) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨Known.cPhContains, 0⟩ [.node ch, v])⟩ ⟨s, fr, .val (.bool b)⟩ := by
  refine Steps.next (step_alg H chk s fr _ _ containsPhAlg containsPhCode containsPhAlg_pin containsPhCode_pin) ?_
  rcases contains_symOf hv with ⟨k, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    refine Steps.trans (hrec _ _) ?_
    csteps
    exact .refl _

theorem contains_child_some (X : Ctx F) (s : State F) (a : AlgId) (nd : F.Node) (sl : Array (Val F)) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (k : NtId) (ch : F.Node)
    (h : F.nodeChild nd k 0 = some (some ch)) :
    step X ⟨s, ⟨a, some nd, sl, kd, p, K, ci⟩ :: fs, .op (.child 5 k)⟩ =
      .inl ⟨s, ⟨a, some nd, sl, kd, p, K, ci⟩ :: fs, .val (.node ch)⟩ := by
  have : childAt (M := F) 5 k nd = Run.pure (.node ch) := by
    unfold childAt
    simp
    split
    · rename_i c hc
      cases h.symm.trans hc
      rfl
    · rename_i hc
      cases h.symm.trans hc
    · rename_i hc
      cases h.symm.trans hc
  simp [step, evalOp, evChild, this, leafV, bindR, Run.pure, Cfg.to, Cfg.top]

theorem contains_child_none (X : Ctx F) (s : State F) (a : AlgId) (nd : F.Node) (sl : Array (Val F)) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (k : NtId)
    (h : ∀ ch, F.nodeChild nd k 0 ≠ some (some ch)) :
    step X ⟨s, ⟨a, some nd, sl, kd, p, K, ci⟩ :: fs, .op (.child 5 k)⟩ =
      .inl ⟨s, ⟨a, some nd, sl, kd, p, K, ci⟩ :: fs, .val .absent⟩ := by
  have : childAt (M := F) 5 k nd = Run.pure .absent := by
    unfold childAt
    simp
    split
    · exact absurd ‹_› (h _)
    · rfl
    · rfl
  simp [step, evalOp, evChild, this, leafV, bindR, Run.pure, Cfg.to, Cfg.top]


/-! ## The walk's symbols -/

theorem contains_sym_beq (a b : Contains.Sym) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> simp [BEq.beq, Contains.instBEqSym.beq]

instance : LawfulBEq Contains.Sym where
  eq_of_beq h := by simpa [contains_sym_beq] using h
  rfl := by simp [contains_sym_beq]

theorem contains_sameIs (D : LeafCtx F) {v w : Val F} {a b : Contains.Sym} (hv : Contains.symOf v = some a)
    (hw : Contains.symOf w = some b) : sameIs D v w = (a == b) := by
  rcases contains_symOf hv with ⟨k, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ <;>
    rcases contains_symOf hw with ⟨k', rfl, rfl⟩ | ⟨t', rfl, rfl⟩ <;>
    simp [sameIs, Val.same] <;> first | rfl | (rw [Bool.eq_iff_iff]; simp)

theorem contains_used {v : Val F} {a : Contains.Sym} (hv : Contains.symOf v = some a) : v.used = v := by
  rcases contains_symOf hv with ⟨k, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ <;> rfl

/-- `symbol is (not) one of` grammar symbols: the walk's test. -/
theorem contains_test (D : LeafCtx F) (neg : Bool) {v : Val F} {sym : Contains.Sym} (hv : Contains.symOf v = some sym)
    (ws : List (Val F)) (ss : List Contains.Sym) (hws : ws.map Contains.symOf = ss.map some) :
    (neg != if false = true then !ws.any (sameIs D v.used) else ws.any (sameIs D v.used)) =
      (neg != ss.contains sym) := by
  have : ws.any (sameIs D v.used) = ss.contains sym := by
    rw [contains_used hv]
    induction ws generalizing ss with
    | nil => cases ss <;> simp_all
    | cons w ws ih =>
      cases ss with
      | nil => simp at hws
      | cons x ss =>
        simp only [List.map_cons, List.cons.injEq] at hws
        simp only [List.any_cons, List.contains_cons, ih ss hws.2, contains_sameIs D hv hws.1]
  simp [this]

theorem contains_atChild {rec : SdoId → F.Node → Option Bool} {nd : F.Node} {s : SdoId} {k : NtId} {b : Bool}
    (h : Contains.atChild rec nd s k = some b) : ∃ ch, F.nodeChild nd k 0 = some (some ch) ∧ rec s ch = some b := by
  unfold Contains.atChild at h
  split at h
  · rename_i c hc
    exact ⟨c, hc, h⟩
  · cases h

theorem contains_any1 {rec : SdoId → F.Node → Option Bool} {nd : F.Node} {s : SdoId} {k : NtId} {b : Bool}
    (h : Contains.anyAt rec nd [(s, k)] = some b) : Contains.atChild rec nd s k = some b := by
  simp only [Contains.anyAt] at h
  split at h
  · rename_i h'; cases h; exact h'
  · rename_i h'; cases h; exact h'
  · cases h

theorem contains_any2 {rec : SdoId → F.Node → Option Bool} {nd : F.Node} {s1 s2 : SdoId} {k1 k2 : NtId} {b : Bool}
    (h : Contains.anyAt rec nd [(s1, k1), (s2, k2)] = some b) :
    (Contains.atChild rec nd s1 k1 = some true ∧ b = true) ∨
      (Contains.atChild rec nd s1 k1 = some false ∧ Contains.atChild rec nd s2 k2 = some b) := by
  rw [Contains.anyAt] at h
  split at h
  · rename_i h'; cases h; exact .inl ⟨h', rfl⟩
  · rename_i h'; exact .inr ⟨h', contains_any1 h⟩
  · cases h

/-! ## Operands -/

/-- `X Contains symbol` (ph-contains) of a child, from the child's read. -/
theorem contains_opPh [PinsHold] (H : Host F) (chk : Bool) (s : State F) (a : AlgId) (nd : F.Node)
    (rest : List (Val F)) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (k : NtId) (b : Bool)
    (hb : Contains.atChild rec nd Known.sdoContains k = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, (v :: rest).toArray, kd, p, .args (.call (.alg ⟨Known.cPhContains, 0⟩)) [] [.bnd 0] :: K, ci⟩ :: fs,
        .op (.child 5 k)⟩
      ⟨s, ⟨a, some nd, (v :: rest).toArray, kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ := by
  obtain ⟨ch, hch, hr⟩ := contains_atChild hb
  refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ hch) ?_
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    exact contains_ph_steps H chk _ _ _ _ hv ch b (hrec Known.sdoContains ch b hr)

/-- SDO `s'` of a child with the symbol, from the child's read. -/
theorem contains_opOn (H : Host F) (chk : Bool) (s : State F) (a : AlgId) (nd : F.Node)
    (rest : List (Val F)) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (s' : SdoId)
    (k : NtId) (b : Bool) (hb : Contains.atChild rec nd s' k = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, (v :: rest).toArray, kd, p, .args (.recv (.sdo s') [.var 0]) [] [] :: K, ci⟩ :: fs,
        .op (.child 5 k)⟩
      ⟨s, ⟨a, some nd, (v :: rest).toArray, kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ := by
  obtain ⟨ch, hch, hr⟩ := contains_atChild hb
  refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ hch) ?_
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    exact hrec s' ch b hr _ _

/-! ## Rows -/

theorem contains_any1_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (k : NtId) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.any [(Known.sdoContains, k)]) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code (containsAny1Code k)⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  have hb' := contains_any1 hb
  cases b
  all_goals
    csteps
    refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec k _ hb') ?_
    csteps
    exact .refl _

theorem contains_cpc1_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (k : NtId) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.any [(Known.sdoComputedPropertyContains, k)]) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code (containsCpc1Code k)⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  have hb' := contains_any1 hb
  csteps
  refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains k _ hb') ?_
  csteps
  refine Steps.trans (contains_res_steps H chk _ _ b) ?_
  csteps
  exact .refl _

theorem contains_cpcPh_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (k : NtId) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.any [(Known.sdoContains, k)]) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code (containsCpcPhCode k)⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  have hb' := contains_any1 hb
  csteps
  refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec k _ hb') ?_
  csteps
  refine Steps.trans (contains_res_steps H chk _ _ b) ?_
  csteps
  exact .refl _

theorem contains_cpc2_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (k1 k2 : NtId)
    (b : Bool) (hb : Contains.runBeh sym rec nd (.any [(Known.sdoComputedPropertyContains, k1), (Known.sdoComputedPropertyContains, k2)]) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v, .unbound], .steps false true false, [], [], none⟩ :: fs, .code (containsCpc2Code k1 k2)⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  rcases contains_any2 hb with ⟨h1, rfl⟩ | ⟨h1, h2⟩
  · csteps
    refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains k1 _ h1) ?_
    csteps
    exact .refl _
  · csteps
    refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains k1 _ h1) ?_
    csteps
    refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains k2 _ h2) ?_
    csteps
    refine Steps.trans (contains_res_steps H chk _ _ b) ?_
    csteps
    exact .refl _


/-- ph-token-nt's steps: the terminal. -/
theorem contains_term_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (k : NtId) (t : String) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨Known.cPhTokenNt, 0⟩ [.nt k [], .term t])⟩
      ⟨s, fr, .val (.term t)⟩ := by
  refine Steps.next (step_alg H chk s fr _ _ containsTermAlg containsTermCode containsTermAlg_pin
    containsTermCode_pin) ?_
  csteps
  exact .refl _

/-- `symbol is |K|`, from the symbol's read. -/
theorem contains_opIs (X : Ctx F) (s : State F) (a : AlgId) (nd : Option F.Node)
    (rest : List (Val F)) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (k : NtId) :
    Steps X
      ⟨s, ⟨a, nd, (v :: rest).toArray, kd, p,
        .args (.bind (.and [.leaf (.isVal false false) [.bound, .const (.nt k [])]])) [] [] :: K, ci⟩ :: fs,
        .op (.var 0)⟩
      ⟨s, ⟨a, nd, (v :: rest).toArray, kd, p, K, ci⟩ :: fs,
        .val (.bool (false != [Contains.Sym.nt k].contains sym))⟩ := by
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    refine Steps.valBool _ (contains_test _ false hv [.nt k []] [.nt k] rfl) ?_
    generalize (false != [Contains.Sym.nt k].contains _) = c
    cases c <;> csteps_to

/-- `symbol is not one of |NewTarget|, |SuperProperty|, |SuperCall|, super, or this`, from the symbol's read. -/
theorem contains_opArrow (X : Ctx F) (s : State F) (a : AlgId) (nd : Option F.Node)
    (rest : List (Val F)) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) :
    Steps X
      ⟨s, ⟨a, nd, (v :: rest).toArray, kd, p,
        .args (.bind (.and [.leaf (.isVal true false)
          [.bound, .const (.nt Known.ntNewTarget []), .const (.nt Known.ntSuperProperty []), .const (.nt Known.ntSuperCall []), .const (.term "super"),
            .const (.term "this")]])) [] [] :: K, ci⟩ :: fs,
        .op (.var 0)⟩
      ⟨s, ⟨a, nd, (v :: rest).toArray, kd, p, K, ci⟩ :: fs,
        .val (.bool (true != Contains.arrowSyms.contains sym))⟩ := by
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    refine Steps.valBool _ (contains_test _ true hv [.nt Known.ntNewTarget [], .nt Known.ntSuperProperty [], .nt Known.ntSuperCall [], .term "super", .term "this"]
      Contains.arrowSyms rfl) ?_
    generalize (true != Contains.arrowSyms.contains _) = c
    cases c <;> csteps_to

/-- `symbol is the |ReservedWord| super`, from the symbol's read. -/
theorem contains_opSuper [PinsHold] (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : Option F.Node)
    (rest : List (Val F)) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, (v :: rest).toArray, kd, p,
        .args (.bind (.and [.leaf (.isVal false false)
          [.bound, .call (.alg ⟨Known.cPhTokenNt, 0⟩) [.const (.nt Known.ntReservedWord []), .const (.term "super")]]])) [] [] :: K, ci⟩ :: fs,
        .op (.var 0)⟩
      ⟨s, ⟨a, nd, (v :: rest).toArray, kd, p, K, ci⟩ :: fs,
        .val (.bool (false != [Contains.Sym.term "super"].contains sym))⟩ := by
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    refine Steps.trans (contains_term_steps H chk _ _ _ _) ?_
    csteps
    refine Steps.valBool _ (contains_test _ false hv [.term "super"] [.term "super"] rfl) ?_
    generalize (false != [Contains.Sym.term "super"].contains _) = c
    cases c <;> csteps_to

theorem contains_isSym_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (k : NtId) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.isSym (.nt k) (.any [(Known.sdoComputedPropertyContains, k)])) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code (containsIsSymCode k)⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  csteps_var
  refine Steps.trans (contains_opIs _ _ _ _ _ _ _ _ _ _ v sym hv k) ?_
  by_cases hc : sym = .nt k
  · subst hc
    simp [Contains.runBeh] at hb
    subst hb
    refine Steps.valBool true (by simp) ?_
    csteps
    exact .refl _
  · refine Steps.valBool false (by simp [hc]) ?_
    simp [Contains.runBeh, Ne.symm hc] at hb
    have hb' := contains_any1 hb
    csteps
    refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains k _ hb') ?_
    csteps
    refine Steps.trans (contains_res_steps H chk _ _ b) ?_
    csteps
    exact .refl _

theorem contains_super_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.isSym (.term "super") (.ret false)) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code containsSuperCode⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  csteps_var
  refine Steps.trans (contains_opSuper H chk _ _ _ _ _ _ _ _ _ v sym hv) ?_
  by_cases hc : sym = .term "super"
  · subst hc
    simp [Contains.runBeh] at hb
    subst hb
    refine Steps.valBool true (by simp) ?_
    csteps
    exact .refl _
  · refine Steps.valBool false (by simp [hc]) ?_
    simp [Contains.runBeh, Ne.symm hc] at hb
    subst hb
    csteps
    exact .refl _

theorem contains_arrow2_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.arrow Contains.arrowSyms (.any [(Known.sdoContains, Known.ntArrowParameters), (Known.sdoContains, Known.ntConciseBody)])) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code containsArrow2Code⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  csteps_var
  refine Steps.trans (contains_opArrow _ _ _ _ _ _ _ _ _ _ v sym hv) ?_
  rw [Contains.runBeh] at hb
  cases hc : Contains.arrowSyms.contains sym
  · rw [hc] at hb
    simp at hb
    subst hb
    csteps
    exact .refl _
  · rw [hc] at hb
    simp only [↓reduceIte, Contains.runBeh] at hb
    rcases contains_any2 hb with ⟨h1, rfl⟩ | ⟨h1, h2⟩
    · csteps
      refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec _ _ h1) ?_
      csteps
      exact .refl _
    · csteps
      refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec _ _ h1) ?_
      csteps
      refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec _ _ h2) ?_
      csteps
      exact .refl _

theorem contains_arrow1_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.arrow Contains.arrowSyms (.any [(Known.sdoContains, Known.ntAsyncConciseBody)])) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code containsArrow1Code⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  csteps_var
  refine Steps.trans (contains_opArrow _ _ _ _ _ _ _ _ _ _ v sym hv) ?_
  rw [Contains.runBeh] at hb
  cases hc : Contains.arrowSyms.contains sym
  · rw [hc] at hb
    simp at hb
    subst hb
    csteps
    exact .refl _
  · rw [hc] at hb
    simp only [↓reduceIte, Contains.runBeh] at hb
    have h1 := contains_any1 hb
    csteps
    refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec _ _ h1) ?_
    csteps
    exact .refl _

theorem contains_arrowDecl_steps (X : Ctx F) (s : State F) (fs : List (Frame F))
    (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.arrow Contains.arrowSyms .decline) = some b) :
    Steps X
      ⟨s, ⟨a, some nd, #[v, .unbound], .steps false true false, [], [], none⟩ :: fs, .code containsArrowDeclCode⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  csteps_var
  refine Steps.trans (contains_opArrow _ _ _ _ _ _ _ _ _ _ v sym hv) ?_
  rw [Contains.runBeh] at hb
  cases hc : Contains.arrowSyms.contains sym
  · rw [hc] at hb
    simp at hb
    subst hb
    csteps
    exact .refl _
  · rw [hc] at hb
    simp [Contains.runBeh] at hb


/-! ## Contains' default definition -/

theorem contains_beq_nt (a b : NtId) : (Contains.Sym.nt a == Contains.Sym.nt b) = (b == a) := by
  rw [Bool.eq_iff_iff]; simp; constructor <;> exact Eq.symm

theorem contains_beq_term (a b : String) : (Contains.Sym.term a == Contains.Sym.term b) = (b == a) := by
  rw [Bool.eq_iff_iff]; simp; constructor <;> exact Eq.symm

theorem contains_beq_nt_term (a : NtId) (b : String) : (Contains.Sym.nt a == Contains.Sym.term b) = false := by
  simp

theorem contains_beq_term_nt (a : String) (b : NtId) : (Contains.Sym.term a == Contains.Sym.nt b) = false := by
  simp

/-- The default definition's loop's body, and its steps after the instance and cover checks. -/
def containsDfltBody : Code :=
  match containsDfltCode with
  | [_, .loop _ _ _ body, _, _] => body
  | _ => []

def containsDfltRest : Code := containsDfltBody.drop 4

/-- `child is an instance of symbol`. -/
def containsInst (x : Val F) (sym : Contains.Sym) : Bool :=
  match x with
  | .leaf _ _ t => sym == .term t
  | .node c => sym == .nt (F.nodeNt c)
  | _ => false

/-- `gstep`, but not at an SDO's call, a test of an instance or the symbol's read either. -/
macro "dstep" : tactic => `(tactic| (
  fail_if_success (show Steps _ ⟨_, _, .op (.leaf .toBool _)⟩ _)
  fail_if_success (show Steps _ ⟨_, _, .op (.var 0)⟩ _)
  cstep))

macro "dsteps" : tactic => `(tactic| repeat dstep)

macro "dsteps_to" : tactic => `(tactic| repeat (first | exact Steps.refl _ | dstep))

theorem contains_inst_steps (X : Ctx F) (s : State F) (a : AlgId) (nd : Option F.Node) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (x x2 : Val F)
    (hx : (∃ n i t, x = .leaf n i t) ∨ (∃ ch, x = .node ch)) :
    Steps X
      ⟨s, ⟨a, nd, #[v, x, x2], kd, p, K, ci⟩ :: fs, .op (.leaf .toBool [.call (.prim Known.pInstanceOf) [.var 1, .bnd 0]])⟩
      ⟨s, ⟨a, nd, #[v, x, x2], kd, p, K, ci⟩ :: fs, .val (.bool (containsInst x sym))⟩ := by
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩ <;>
    rcases hx with ⟨n, i, t', rfl⟩ | ⟨ch, rfl⟩
  all_goals
    csteps
    refine Steps.valBool _ ?_ (.refl _)
    simp only [containsInst, contains_beq_nt, contains_beq_term, contains_beq_nt_term, contains_beq_term_nt]
    try rfl

/-- `this Parse Node is an instance of the production`. -/
theorem contains_prod_steps (X : Ctx F) (s : State F) (a : AlgId) (nd : F.Node) (sl : Array (Val F)) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (ps : List ProdId) :
    Steps X
      ⟨s, ⟨a, some nd, sl, kd, p, K, ci⟩ :: fs,
        .op (.leaf .toBool [.call (.prim Known.pInstanceOf) [.node, .const (.prod ps)]])⟩
      ⟨s, ⟨a, some nd, sl, kd, p, K, ci⟩ :: fs, .val (.bool (ps.contains (F.nodeProd nd)))⟩ := by
  csteps
  exact .refl _

/-- The test of the sort of the nonterminals, of a grammar symbol. -/
theorem contains_sort56_step (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (y : Val F) (b : Bool) (hy : (∃ k as, y = .nt k as ∧ b = true) ∨ (∃ t, y = .term t ∧ b = false)) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort Known.sNonterminal y)⟩ = .inl ⟨s, fr, .val (.bool b)⟩ := by
  simp only [step, invoke, spec_P, contains_sort56]
  rcases hy with ⟨k, as, rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  · simp only [sortTest, contains_sort56]
    rfl
  · simp only [sortTest, contains_sort56]
    rfl

/-- `child is a nonterminal`. -/
theorem contains_isNt_steps (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : Option F.Node) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v x x2 : Val F) (b : Bool)
    (hx : (∃ n i t, x = .leaf n i t ∧ b = false) ∨ (∃ ch, x = .node ch ∧ b = true)) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, #[v, x, x2], kd, p, K, ci⟩ :: fs,
        .op (.leaf .toBool [.call (.prim Known.pInstanceOf) [.var 1, .const (.data (.sort Known.sNonterminal))]])⟩
      ⟨s, ⟨a, nd, #[v, x, x2], kd, p, K, ci⟩ :: fs, .val (.bool b)⟩ := by
  rcases hx with ⟨n, i, t', rfl, rfl⟩ | ⟨ch, rfl, rfl⟩
  · csteps
    refine Steps.next (contains_sort56_step H chk _ _ _ false (.inr ⟨_, rfl, rfl⟩)) ?_
    csteps
    exact .refl _
  · csteps
    refine Steps.next (contains_sort56_step H chk _ _ _ true (.inl ⟨_, _, rfl, rfl⟩)) ?_
    csteps
    exact .refl _


/-- The walk's `await`: the symbol is |AwaitExpression| and the node the cover's production. -/
def containsAwait (sym : Contains.Sym) (nd : F.Node) : Bool :=
  sym == .nt Known.ntAwaitExpression && [Known.prodAwaitCover].contains (F.nodeProd nd)

/-- The first two steps where the child is an instance of the symbol, or the cover's condition holds: *true*. -/
theorem contains_read_true (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : F.Node) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (x x2 : Val F)
    (hx : (∃ n i t, x = .leaf n i t) ∨ (∃ ch, x = .node ch))
    (h : (containsInst x sym || containsAwait sym nd) = true) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v, x, x2], .steps false true true, p, K, ci⟩ :: fs, .code containsDfltBody⟩
      ⟨s, fs, .val (.bool true)⟩ := by
  dsteps
  refine Steps.trans (contains_inst_steps _ _ _ _ _ _ _ _ _ v sym hv x x2 hx) ?_
  cases hi : containsInst x sym
  · unfold containsAwait at h
    rw [hi, Bool.false_or, Bool.and_eq_true] at h
    dsteps
    refine Steps.trans (contains_opIs _ _ _ _ _ _ _ _ _ _ v sym hv Known.ntAwaitExpression) ?_
    refine Steps.valBool true (by simpa using h.1) ?_
    dsteps
    refine Steps.trans (contains_prod_steps _ _ _ _ _ _ _ _ _ _ _) ?_
    rw [h.2]
    dsteps
    exact .refl _
  · dsteps
    exact .refl _

/-- The first two steps where the child is not an instance of the symbol and the cover's condition does not hold:
the steps after them. -/
theorem contains_read_false (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : F.Node) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (x x2 : Val F)
    (hx : (∃ n i t, x = .leaf n i t) ∨ (∃ ch, x = .node ch))
    (h : (containsInst x sym || containsAwait sym nd) = false) :
    ∃ p', Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v, x, x2], .steps false true true, p, K, ci⟩ :: fs, .code containsDfltBody⟩
      ⟨s, ⟨a, some nd, #[v, x, x2], .steps false true true, p', K, ci⟩ :: fs, .code containsDfltRest⟩ := by
  rw [Bool.or_eq_false_iff] at h
  obtain ⟨hi, ha⟩ := h
  unfold containsAwait at ha
  refine ⟨[2, 1], ?_⟩
  dsteps
  refine Steps.trans (contains_inst_steps _ _ _ _ _ _ _ _ _ v sym hv x x2 hx) ?_
  rw [hi]
  dsteps
  refine Steps.trans (contains_opIs _ _ _ _ _ _ _ _ _ _ v sym hv Known.ntAwaitExpression) ?_
  cases hs : (sym == Contains.Sym.nt Known.ntAwaitExpression)
  · refine Steps.valBool false (by simpa using hs) ?_
    dsteps_to
  · refine Steps.valBool true (by simpa using hs) ?_
    rw [hs, Bool.true_and] at ha
    dsteps
    refine Steps.trans (contains_prod_steps _ _ _ _ _ _ _ _ _ _ _) ?_
    rw [ha]
    dsteps_to

/-- The steps after the instance and cover checks at a terminal: none. -/
theorem contains_rest_leaf (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : Option F.Node) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v x2 : Val F) (n : F.Node) (i : Nat) (t : String) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, #[v, .leaf n i t, x2], kd, p, K, ci⟩ :: fs, .code containsDfltRest⟩
      ⟨s, ⟨a, nd, #[v, .leaf n i t, x2], kd, [3, 1], K, ci⟩ :: fs, .done⟩ := by
  dsteps
  refine Steps.trans (contains_isNt_steps H chk _ _ _ _ _ _ _ _ _ _ _ false (.inl ⟨_, _, _, rfl, rfl⟩)) ?_
  dsteps_to

/-- The steps after the instance and cover checks at a child node that Contains the symbol: *true*. -/
theorem contains_rest_true [PinsHold] (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : Option F.Node) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (x2 : Val F) (ch : F.Node)
    (hrec : ∀ (st : State F) (fr : List (Frame F)),
      Steps (Ctx.spec Engine.P' H chk) ⟨st, fr, .invoke (.sdo Known.sdoContains ch [v])⟩ ⟨st, fr, .val (.bool true)⟩) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, #[v, .node ch, x2], .steps false true true, p, K, ci⟩ :: fs, .code containsDfltRest⟩
      ⟨s, fs, .val (.bool true)⟩ := by
  dsteps
  refine Steps.trans (contains_isNt_steps H chk _ _ _ _ _ _ _ _ _ _ _ true (.inr ⟨_, rfl, rfl⟩)) ?_
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    dsteps
    refine Steps.trans (contains_ph_steps H chk _ _ _ _ hv ch true hrec) ?_
    dsteps
    refine Steps.trans (contains_res_steps H chk _ _ true) ?_
    csteps
    exact .refl _

/-- The steps after the instance and cover checks at a child node that does not Contain the symbol: none. -/
theorem contains_rest_false [PinsHold] (H : Host F) (chk : Bool) (s : State F) (a : AlgId)
    (nd : Option F.Node) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (x2 : Val F) (ch : F.Node)
    (hrec : ∀ (st : State F) (fr : List (Frame F)),
      Steps (Ctx.spec Engine.P' H chk) ⟨st, fr, .invoke (.sdo Known.sdoContains ch [v])⟩ ⟨st, fr, .val (.bool false)⟩) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, #[v, .node ch, x2], kd, p, K, ci⟩ :: fs, .code containsDfltRest⟩
      ⟨s, ⟨a, nd, #[v, .node ch, .bool false], kd, [2, 3, 1], K, ci⟩ :: fs, .done⟩ := by
  dsteps
  refine Steps.trans (contains_isNt_steps H chk _ _ _ _ _ _ _ _ _ _ _ true (.inr ⟨_, rfl, rfl⟩)) ?_
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    dsteps
    refine Steps.trans (contains_ph_steps H chk _ _ _ _ hv ch false hrec) ?_
    dsteps
    refine Steps.trans (contains_res_steps H chk _ _ false) ?_
    repeat (first | exact Steps.refl _ | cstep)

/-! ### The loop over the children -/

/-- A round's head at a terminal of the production: the child bound to it. -/
theorem contains_kids_term (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Slot) (o : Option Op) (p : List Nat)
    (body : Code) (nd : F.Node) (i : Nat) (j : Int) (r : Nat) (t : String)
    (h : (X.P.terms (F.nodeProd nd)).lookup i = some t) :
    step X ⟨s, fr, .loop .round ⟨some x, .kids o, p, body, .kids nd i (.int j), r⟩⟩ =
      loopBody ((⟨s, fr, .loop .round ⟨some x, .kids o, p, body, .kids nd i (.int j), r⟩⟩ : Cfg F).setSlot x
          (.leaf nd i t))
        ⟨some x, .kids o, p, body, .kids nd (i + 1) (.int j), r⟩ := by
  simp [step, loopStep, iterNext, bindR, h, Run.pure]

/-- A round's head at a child node: the child bound to it. -/
theorem contains_kids_node (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Slot) (o : Option Op) (p : List Nat)
    (body : Code) (nd : F.Node) (i : Nat) (j : Nat) (r : Nat) (c : F.Node)
    (h : (X.P.terms (F.nodeProd nd)).lookup i = none) (hc : (F.nodeKids nd)[j]? = some c) :
    step X ⟨s, fr, .loop .round ⟨some x, .kids o, p, body, .kids nd i (.int j), r⟩⟩ =
      loopBody ((⟨s, fr, .loop .round ⟨some x, .kids o, p, body, .kids nd i (.int j), r⟩⟩ : Cfg F).setSlot x
          (.node c))
        ⟨some x, .kids o, p, body, .kids nd (i + 1) (.int ((j + 1 : Nat) : Int)), r⟩ := by
  have hi : j < (F.nodeKids nd).size := by
    rcases Nat.lt_or_ge j (F.nodeKids nd).size with h' | h'
    · exact h'
    · simp [Array.getElem?_eq_none h'] at hc
  have hv' : (F.nodeKids nd)[j] = c := by simpa [Array.getElem?_eq_getElem hi] using hc
  simp [step, loopStep, iterNext, bindR, h, Run.pure, Model.MathVal.lt, Model.MathVal.idx, hv', hi,
    Model.MathVal.add]

/-- A round's head past the children: the loop's end. -/
theorem contains_kids_end (X : Ctx F) (s : State F) (fr : List (Frame F)) (x : Option Slot) (o : Option Op)
    (p : List Nat) (body : Code) (nd : F.Node) (i : Nat) (j : Nat) (r : Nat)
    (h : (X.P.terms (F.nodeProd nd)).lookup i = none) (hj : ¬ j < (F.nodeKids nd).size) :
    step X ⟨s, fr, .loop .round ⟨x, .kids o, p, body, .kids nd i (.int j), r⟩⟩ =
      loopEnd ⟨s, fr, .loop .round ⟨x, .kids o, p, body, .kids nd i (.int j), r⟩⟩
        ⟨x, .kids o, p, body, .kids nd i (.int j), r⟩ := by
  simp [step, loopStep, iterNext, bindR, h, Run.pure, Model.MathVal.lt, hj]


theorem contains_drop_cons {α : Type} {l : List α} {j : Nat} {c : α} {ks : List α} (h : l.drop j = c :: ks) :
    l[j]? = some c ∧ l.drop (j + 1) = ks := by
  constructor
  · have := congrArg (·[0]?) h
    simpa [List.getElem?_drop] using this
  · have := congrArg (List.drop 1) h
    simpa [List.drop_drop, Nat.add_comm] using this

def containsDfltTail : Code := [.site [2], .ret (.const (.val .false))]

/-- The default definition's loop from a round's head: the walk's answer from there. -/
theorem contains_dflt_loop [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (await : Bool)
    (haw : await = containsAwait sym nd) :
    ∀ (f i j : Nat) (q : List Nat) (r : Nat) (x1 x2 : Val F) (b : Bool),
      Contains.dfltAt.go sym rec (Engine.P.terms (F.nodeProd nd)) await f i ((F.nodeKids nd).toList.drop j) = some b →
      Steps (Ctx.spec Engine.P' H chk)
        ⟨s, ⟨⟨Known.cStaticContains, 0⟩, some nd, #[v, x1, x2], .steps false true true, q, [.seq containsDfltTail], none⟩ :: fs,
          .loop .round ⟨some 1, .kids none, [1], containsDfltBody, .kids nd i (.int j), r⟩⟩
        ⟨s, fs, .val (.bool b)⟩ := by
  intro f
  induction f with
  | zero =>
    intro i j q r x1 x2 b h
    simp [Contains.dfltAt.go] at h
  | succ f ih =>
    intro i j q r x1 x2 b h
    rw [Contains.dfltAt.go.eq_def] at h
    cases hl : (Engine.P.terms (F.nodeProd nd)).lookup i with
    | some t =>
      simp only [hl] at h
      refine Steps.next (contains_kids_term _ _ _ _ _ _ _ _ _ _ _ t hl) ?_
      dsimp only [loopBody, Cfg.setSlot, Cfg.atPath, Cfg.push, Cfg.mapTop, Cfg.to]
      simp only [List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero]
      cases hc : (sym == Contains.Sym.term t || await)
      · rw [hc] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨p', hs⟩ := contains_read_false H chk s _ nd _ _ _ fs v sym hv (.leaf nd i t) x2
          (.inl ⟨_, _, _, rfl⟩) (by rw [← haw]; exact hc)
        refine Steps.trans hs ?_
        refine Steps.trans (contains_rest_leaf H chk _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
        csteps
        exact ih (i + 1) j _ _ _ _ b h
      · rw [hc] at h
        simp only [↓reduceIte] at h
        cases h
        exact contains_read_true H chk s _ nd _ _ _ fs v sym hv (.leaf nd i t) x2
          (.inl ⟨_, _, _, rfl⟩) (by rw [← haw]; exact hc)
    | none =>
      cases hk : (F.nodeKids nd).toList.drop j with
      | nil =>
        simp only [hl, hk] at h
        cases h
        have hj : ¬ j < (F.nodeKids nd).size := by
          have := List.drop_eq_nil_iff.mp hk
          simpa using this
        refine Steps.next (contains_kids_end _ _ _ _ _ _ _ _ _ _ _ hl hj) ?_
        dsimp only [loopEnd, Cfg.atPath, Cfg.mapTop, Cfg.to]
        csteps
        exact .refl _
      | cons c ks =>
        simp only [hl, hk] at h
        obtain ⟨hcj, hks⟩ := contains_drop_cons hk
        have hcj' : (F.nodeKids nd)[j]? = some c := by simpa using hcj
        refine Steps.next (contains_kids_node _ _ _ _ _ _ _ _ _ _ _ c hl hcj') ?_
        dsimp only [loopBody, Cfg.setSlot, Cfg.atPath, Cfg.push, Cfg.mapTop, Cfg.to]
        simp only [List.setIfInBounds_toArray, List.set_cons_succ, List.set_cons_zero]
        cases hc : (sym == Contains.Sym.nt (F.nodeNt c) || await)
        · rw [hc] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨p', hs⟩ := contains_read_false H chk s _ nd _ _ _ fs v sym hv (.node c) x2
            (.inr ⟨_, rfl⟩) (by rw [← haw]; exact hc)
          refine Steps.trans hs ?_
          cases hr : rec Contains.sdoC c with
          | none => rw [hr] at h; cases h
          | some b1 =>
            rw [hr] at h
            cases b1
            · dsimp only at h
              refine Steps.trans (contains_rest_false H chk _ _ _ _ _ _ _ _ v sym hv _ c (hrec Known.sdoContains c false hr)) ?_
              csteps
              rw [← hks] at h
              exact ih (i + 1) (j + 1) _ _ _ _ b h
            · dsimp only at h
              cases h
              exact contains_rest_true H chk _ _ _ _ _ _ _ v sym hv _ c (hrec Known.sdoContains c true hr)
        · rw [hc] at h
          simp only [↓reduceIte] at h
          cases h
          exact contains_read_true H chk s _ nd _ _ _ fs v sym hv (.node c) x2
            (.inr ⟨_, rfl⟩) (by rw [← haw]; exact hc)

theorem contains_foldl_cons {α : Type} (l acc : List α) :
    l.foldl (fun acc c => c :: acc) acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- Contains' default definition's steps: the walk's answer. -/
theorem contains_dflt_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fs : List (Frame F))
    (nd : F.Node) (v : Val F) (sym : Contains.Sym) (hv : Contains.symOf v = some sym)
    (rec : SdoId → F.Node → Option Bool) (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (b : Bool)
    (T : Contains.Tab) (hTt : T.terms = Engine.P.terms)
    (hb : Contains.dfltAt T sym rec nd (some ([Known.prodAwaitCover], Known.ntAwaitExpression)) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, algFrame containsDfltAlg (some nd) (containsDfltAlg.args [v]) containsDfltAlg.header.rc true true :: fs,
        .code containsDfltCode⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  have hks : (F.seqFoldl (fun acc c => c :: acc) [] (F.nodeKids nd)).reverse = (F.nodeKids nd).toList := by
    show (Array.foldl (fun acc c => c :: acc) [] (F.nodeKids nd)).reverse = _
    rw [← Array.foldl_toList, contains_foldl_cons]
    simp
  unfold Contains.dfltAt at hb
  rw [hks, hTt] at hb
  have hgo := contains_dflt_loop H chk s fs nd v sym hv rec hrec (containsAwait sym nd) rfl
    Contains.depthMax 0 0
  rcases contains_symOf hv with ⟨k', rfl, rfl⟩ | ⟨t, rfl, rfl⟩
  all_goals
    csteps
    exact hgo _ _ _ _ b hb

/-! ## ClassTail -/

theorem contains_classTail_steps [PinsHold] (H : Host F) (chk : Bool) (s : State F)
    (fs : List (Frame F)) (a : AlgId) (nd : F.Node) (v : Val F) (sym : Contains.Sym)
    (hv : Contains.symOf v = some sym) (rec : SdoId → F.Node → Option Bool)
    (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (b : Bool)
    (hb : Contains.runBeh sym rec nd (.classTail Known.ntClassHeritage Known.ntClassBody Known.sdoComputedPropertyContains) = some b) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, some nd, #[v], .steps false true false, [], [], none⟩ :: fs, .code containsClassTailCode⟩
      ⟨s, fs, .val (.bool b)⟩ := by
  rw [Contains.runBeh] at hb
  generalize hp : F.nodeChild nd Known.ntClassHeritage 0 = o at hb
  csteps_var
  refine Steps.trans (contains_opIs _ _ _ _ _ _ _ _ _ _ v sym hv Known.ntClassBody) ?_
  by_cases h1 : sym = .nt Known.ntClassBody
  · subst h1
    simp at hb
    subst hb
    refine Steps.valBool true (by simp) ?_
    csteps
    exact .refl _
  · refine Steps.valBool false (by simp [h1]) ?_
    csteps_var
    refine Steps.trans (contains_opIs _ _ _ _ _ _ _ _ _ _ v sym hv Known.ntClassHeritage) ?_
    by_cases h2 : sym = .nt Known.ntClassHeritage
    · subst h2
      refine Steps.valBool true (by simp) ?_
      simp only [show (Contains.Sym.nt Known.ntClassHeritage == Contains.Sym.nt Known.ntClassBody) = false from by
            simp [Known.ntClassHeritage, Known.ntClassBody],
        ↓reduceIte, show (Contains.Sym.nt Known.ntClassHeritage == Contains.Sym.nt Known.ntClassHeritage) = true from by simp] at hb
      csteps
      rcases o with _ | _ | ch
      · cases hb
        refine Steps.next (contains_child_none _ _ _ _ _ _ _ _ _ _ _ (by rw [hp]; simp)) ?_
        csteps
        exact .refl _
      · cases hb
        refine Steps.next (contains_child_none _ _ _ _ _ _ _ _ _ _ _ (by rw [hp]; simp)) ?_
        csteps
        exact .refl _
      · cases hb
        refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ hp) ?_
        csteps
        exact .refl _
    · refine Steps.valBool false (by simp [h2]) ?_
      simp only [show (sym == Contains.Sym.nt Known.ntClassBody) = false from by simp [h1], Bool.false_eq_true,
        ↓reduceIte, show (sym == Contains.Sym.nt Known.ntClassHeritage) = false from by simp [h2]] at hb
      csteps
      rcases o with _ | _ | ch
      · simp only [Bool.false_eq_true, ↓reduceIte] at hb
        refine Steps.next (contains_child_none _ _ _ _ _ _ _ _ _ _ _ (by rw [hp]; simp)) ?_
        csteps
        refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains Known.ntClassBody _ hb) ?_
        csteps
        refine Steps.trans (contains_res_steps H chk _ _ b) ?_
        csteps
        exact .refl _
      · simp only [Bool.false_eq_true, ↓reduceIte] at hb
        refine Steps.next (contains_child_none _ _ _ _ _ _ _ _ _ _ _ (by rw [hp]; simp)) ?_
        csteps
        refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains Known.ntClassBody _ hb) ?_
        csteps
        refine Steps.trans (contains_res_steps H chk _ _ b) ?_
        csteps
        exact .refl _
      · simp only [↓reduceIte] at hb
        refine Steps.next (contains_child_some _ _ _ _ _ _ _ _ _ _ _ _ hp) ?_
        csteps
        cases hh : Contains.atChild rec nd Contains.sdoC Known.ntClassHeritage with
        | none => rw [hh] at hb; cases hb
        | some b1 =>
          rw [hh] at hb
          cases b1
          · dsimp only at hb
            refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.ntClassHeritage _ hh) ?_
            csteps
            refine Steps.trans (contains_opOn H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.sdoComputedPropertyContains Known.ntClassBody _ hb) ?_
            csteps
            refine Steps.trans (contains_res_steps H chk _ _ b) ?_
            csteps
            exact .refl _
          · cases hb
            refine Steps.trans (contains_opPh H chk _ _ _ _ _ _ _ _ _ v sym hv rec hrec Known.ntClassHeritage _ hh) ?_
            csteps
            exact .refl _

/-! ## The rows of the program -/

theorem contains_algId_eq {a b : AlgId} (h : (a == b) = true) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have h' : (a1 == b1 && a2 == b2) = true := h
  simp at h'
  simp [h'.1, h'.2]

theorem contains_lookup_mem {β : Type} {a : AlgId} {l : List (AlgId × β)} {x : β} (h : l.lookup a = some x) :
    (a, x) ∈ l := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    obtain ⟨k, w⟩ := y
    rw [List.lookup] at h
    split at h
    · rename_i heq
      cases h
      rw [contains_algId_eq heq]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- What the walk needs of the program's rows: a row of Contains or ComputedPropertyContains with one of the
ids of `containsShapes` has that many variables, and its production's code is that code. -/
def ContainsRows : Prop :=
  ∀ (s : SdoId) (k : ProdId) (r : Ecma.SdoRow) (n : Nat) (code : Code), (s = Known.sdoContains ∨ s = Known.sdoComputedPropertyContains) → Engine.P.row s k = some r →
    containsShapes.lookup r.id = some (n, code) → r.vars.size = n ∧ Engine.P'.row s k = some code

/-- An SDO's obligation: at a call of it, the entry's value is the machine's (`Sound.sdo`). -/
def SdoRowOk (X : Ctx F) (s : SdoId) (e : F.Node → List (Val F) → Option (Run F (Val F))) : Prop :=
  ∀ (c : Cfg F) (nd : F.Node) (vs : List (Val F)) (r : Run F (Val F)), c.ctl = .invoke (.sdo s nd vs) →
    e nd vs = some r → Sim X c (leafV c r)

/-- A continuation pushed on the frames (`Cfg.push`). -/
def containsPush (fr : List (Frame F)) (k : Kont F) : List (Frame F) :=
  match fr with
  | f :: fs => { f with konts := k :: f.konts } :: fs
  | [] => [⟨⟨0, 0⟩, none, #[], .eval, [], [k], none⟩]

/-- The scope of the Parse Nodes being evaluated, undone as the value returns. -/
theorem contains_scope_ret (X : Ctx F) (s : State F) (fr : List (Frame F)) (o i : List F.Node) (v : Val F) :
    Steps X ⟨s, containsPush fr (.scope (.nodes o i)), .val v⟩ ⟨{ s with evalNodes := o }, fr, .val v⟩ := by
  cases fr with
  | nil =>
    mstep
    mstep
    exact .refl _
  | cons f fs =>
    mstep
    exact .refl _

theorem contains_enter (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (sd : SdoId) (nd : F.Node) (v : Val F) (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ =
      sdoEnter (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ sd nd [v] := by
  rcases hsd with rfl | rfl <;> simp [step, invoke, Known.sdoEarlyErrors, Known.sdoContains, Known.sdoComputedPropertyContains]

theorem contains_arity {sd : SdoId} (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) : Engine.P.sdoArity sd = 1 := by
  rcases hsd with rfl | rfl
  · exact contains_arity23
  · exact contains_arity24

theorem contains_rc {sd : SdoId} (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) : Engine.P.sdoRc sd = false := by
  rcases hsd with rfl | rfl
  · exact contains_rc23
  · exact contains_rc24

theorem contains_slots1 {v : Val F} {sym : Contains.Sym} (hv : Contains.symOf v = some sym) :
    initSlots 1 (padArgs 1 ([v].map Val.used)) = #[v] := by
  rcases contains_symOf hv with ⟨k, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ <;> rfl

theorem contains_slots2 {v : Val F} {sym : Contains.Sym} (hv : Contains.symOf v = some sym) :
    initSlots 2 (padArgs 1 ([v].map Val.used)) = #[v, .unbound] := by
  rcases contains_symOf hv with ⟨k, rfl, rfl⟩ | ⟨t, rfl, rfl⟩ <;> rfl

/-- The call at a production with a row: the row's steps in its frame, under the scope. -/
theorem contains_at_row (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (sd : SdoId) (nd : F.Node) (v : Val F) (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) (r : Ecma.SdoRow) (sl : Array (Val F)) (code : Code)
    (b : Bool) (hrow : Engine.P.row sd (F.nodeProd nd) = some r)
    (hsl : initSlots r.vars.size (padArgs (Engine.P.sdoArity sd) ([v].map Val.used)) = sl)
    (hcode : Engine.P'.row sd (F.nodeProd nd) = some code)
    (hsteps : ∀ (s' : State F) (fs' : List (Frame F)), Steps (Ctx.spec Engine.P' H chk)
      ⟨s', ⟨r.id, some nd, sl, .steps false true false, [], [], none⟩ :: fs', .code code⟩
      ⟨s', fs', .val (.bool b)⟩) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ ⟨s, fr, .val (.bool b)⟩ := by
  have hrc : (Ctx.spec Engine.P' H chk).rowCode sd (F.nodeProd nd) = code := by
    show (Engine.P'.row _ _).getD _ = _
    rw [hcode]; rfl
  have he : step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ =
      .inl ⟨{ s with evalNodes := nd :: s.evalNodes },
        ⟨r.id, some nd, sl, .steps false true false, [], [], none⟩ ::
          containsPush fr (.scope (.nodes s.evalNodes (nd :: s.evalNodes))), .code code⟩ := by
    rw [contains_enter H chk s fr sd nd v hsd]
    unfold sdoEnter
    simp only [spec_P, hrow, hrc, hsl, contains_rc hsd]
    cases fr <;> rfl
  exact Steps.next he (Steps.trans (hsteps _ _) (contains_scope_ret _ _ fr _ _ _))

/-- The call at a production without a row, of an SDO whose default definition is Contains'. -/
theorem contains_at_dflt [PinsHold] (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (sd : SdoId) (nd : F.Node) (v : Val F) (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) (b : Bool)
    (hrow : Engine.P.row sd (F.nodeProd nd) = none) (hd : Engine.P.sdoDefault sd = some ⟨Known.cStaticContains, 0⟩)
    (hsteps : ∀ (s' : State F) (fs' : List (Frame F)), Steps (Ctx.spec Engine.P' H chk)
      ⟨s', algFrame containsDfltAlg (some nd) (containsDfltAlg.args [v]) containsDfltAlg.header.rc true true :: fs',
        .code containsDfltCode⟩
      ⟨s', fs', .val (.bool b)⟩) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ ⟨s, fr, .val (.bool b)⟩ := by
  have hcode : (Ctx.spec Engine.P' H chk).algCode containsDfltAlg.id = containsDfltCode :=
    algCode_pin H chk _ _ containsDfltCode_pin
  have he : step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ =
      .inl ⟨{ s with evalNodes := nd :: s.evalNodes },
        algFrame containsDfltAlg (some nd) (containsDfltAlg.args [v]) containsDfltAlg.header.rc true true ::
          containsPush fr (.scope (.nodes s.evalNodes (nd :: s.evalNodes))), .code containsDfltCode⟩ := by
    rw [contains_enter H chk s fr sd nd v hsd]
    unfold sdoEnter
    simp only [spec_P, hrow, hd, Option.bind_some, containsDfltAlg_pin, enterAlg, hcode]
    cases fr <;> rfl
  exact Steps.next he (Steps.trans (hsteps _ _) (contains_scope_ret _ _ fr _ _ _))

/-- The call at a chain production, of an SDO without a default definition: the call at its child. -/
theorem contains_at_chain (H : Host F) (chk : Bool) (s : State F) (fr : List (Frame F))
    (sd : SdoId) (nd : F.Node) (v : Val F) (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) (b : Bool) (k : NtId) (ch : F.Node)
    (hrow : Engine.P.row sd (F.nodeProd nd) = none) (hd : (Engine.P.sdoDefault sd).bind Engine.P.alg = none)
    (hk : Engine.P.chain (F.nodeProd nd) = some k) (hch : F.nodeChild nd k 0 = some (some ch))
    (hsteps : ∀ (s' : State F) (fs' : List (Frame F)), Steps (Ctx.spec Engine.P' H chk)
      ⟨s', fs', .invoke (.sdo sd ch [v])⟩ ⟨s', fs', .val (.bool b)⟩) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ ⟨s, fr, .val (.bool b)⟩ := by
  have he : step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ =
      .inl ⟨{ s with evalNodes := nd :: s.evalNodes },
          containsPush fr (.scope (.nodes s.evalNodes (nd :: s.evalNodes))), .invoke (.sdo sd ch [v])⟩ := by
    rw [contains_enter H chk s fr sd nd v hsd]
    unfold sdoEnter
    simp only [spec_P, hrow, hd, hk]
    have hch' : Engine.Model.nodeChild nd k 0 = some (some ch) := hch
    rw [hch']
    cases fr <;> rfl
  exact Steps.next he (Steps.trans (hsteps _ _) (contains_scope_ret _ _ fr _ _ _))

/-- The call at a production with a row the walk answers at: the row's steps. -/
theorem contains_row_dispatch [PinsHold] (H : Host F) (chk : Bool) (hrows : ContainsRows)
    (s : State F) (fr : List (Frame F)) (sd : SdoId) (nd : F.Node) (v : Val F) (sym : Contains.Sym)
    (hv : Contains.symOf v = some sym) (hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains) (r : Ecma.SdoRow)
    (hrow : Engine.P.row sd (F.nodeProd nd) = some r) (rec : SdoId → F.Node → Option Bool)
    (hrec : ContainsRec (Ctx.spec Engine.P' H chk) v rec) (beh : Contains.Beh)
    (hbeh : Contains.behs.lookup r.id = some beh) (b : Bool) (hb : Contains.runBeh sym rec nd beh = some b) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sdo sd nd [v])⟩ ⟨s, fr, .val (.bool b)⟩ := by
  have hm := contains_lookup_mem hbeh
  simp only [Contains.behs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩ | ⟨hid, rfl⟩
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsClassTailCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_classTail_steps H chk s' fs' _ nd v sym hv rec hrec b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsArrow2Code) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_arrow2_steps H chk s' fs' _ nd v sym hv rec hrec b hb
  · simp [Contains.runBeh] at hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsArrow1Code) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_arrow1_steps H chk s' fs' _ nd v sym hv rec hrec b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 2 (containsArrowDeclCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v, .unbound] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots2 hv) hcode fun s' fs' => ?_
    exact contains_arrowDecl_steps _ s' fs' _ nd v sym hv rec b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsIsSymCode Known.ntMethodDefinition) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_isSym_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsAny1Code Known.ntMemberExpression) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_any1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsSuperCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_super_steps H chk s' fs' _ nd v sym hv rec b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsAny1Code Known.ntCallExpression) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_any1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsAny1Code Known.ntOptionalChain) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_any1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsCpcPhCode Known.ntComputedPropertyName) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_cpcPh_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsCpc1Code Known.ntClassElementName) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_cpc1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsCpc1Code Known.ntClassElementName) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_cpc1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsCpc1Code Known.ntClassElementName) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_cpc1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 2 (containsCpc2Code Known.ntClassElementList Known.ntClassElement) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v, .unbound] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots2 hv) hcode fun s' fs' => ?_
    exact contains_cpc2_steps H chk s' fs' _ nd v sym hv rec hrec _ _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsRetCode) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    obtain rfl : false = b := by simpa [Contains.runBeh] using hb
    exact contains_ret_steps _ s' fs' _ nd _
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsCpc1Code Known.ntClassElementName) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_cpc1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb
  · obtain ⟨hn, hcode⟩ := hrows sd (F.nodeProd nd) r 1 (containsCpc1Code Known.ntClassElementName) hsd hrow (by rw [hid]; rfl)
    refine contains_at_row H chk s fr sd nd v hsd r #[v] _ b hrow
      (by rw [hn, contains_arity hsd]; exact contains_slots1 hv) hcode fun s' fs' => ?_
    exact contains_cpc1_steps H chk s' fs' _ nd v sym hv rec hrec _ b hb


/-! ## The walk -/

/-- The walk's answers, at any depth, are the machine's. -/
theorem contains_walk [PinsHold] (H : Host F) (chk : Bool) (hrows : ContainsRows) (v : Val F)
    (sym : Contains.Sym) (hv : Contains.symOf v = some sym) (T : Contains.Tab)
    (hT : ∀ s p, T.row s p = (Engine.P.row s p).map (·.id))
    (hTd : ∀ s, T.dflt s = (Engine.P.sdoDefault s).filter (fun a => (Engine.P.alg a).isSome))
    (hTc : T.chain = Engine.P.chain) (hTt : T.terms = Engine.P.terms) :
    ∀ n, ContainsRec (Ctx.spec Engine.P' H chk) v (Contains.walk T sym n) := by
  intro n
  induction n with
  | zero =>
    intro sd nd b h
    simp [Contains.walk] at h
  | succ n ih =>
    intro sd nd b h st fr
    rw [Contains.walk] at h
    unfold Contains.step at h
    have hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains := by
      by_cases hsd : sd = Known.sdoContains ∨ sd = Known.sdoComputedPropertyContains
      · exact hsd
      · exfalso
        have : (!(sd == Contains.sdoC || sd == Contains.sdoCPC)) = true := by
          simp [Contains.sdoC, Contains.sdoCPC]
          exact ⟨fun h => hsd (.inl h), fun h => hsd (.inr h)⟩
        rw [this] at h
        simp at h
    have hd : (!(sd == Contains.sdoC || sd == Contains.sdoCPC)) = false := by
      rcases hsd with rfl | rfl <;> rfl
    rw [hd] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    rw [hT, hTd, hTc] at h
    split at h
    · rename_i a heq
      cases hrow : Engine.P.row sd (F.nodeProd nd) with
      | none => rw [hrow] at heq; cases heq
      | some r =>
        rw [hrow] at heq
        cases heq
        cases hbeh : Contains.behs.lookup r.id with
        | none => rw [hbeh] at h; cases h
        | some beh =>
          rw [hbeh] at h
          exact contains_row_dispatch H chk hrows st fr sd nd v sym hv hsd r hrow _ ih beh hbeh b h
    · rename_i heq
      have hrow : Engine.P.row sd (F.nodeProd nd) = none := by
        cases hrow : Engine.P.row sd (F.nodeProd nd) with
        | none => rfl
        | some r => rw [hrow] at heq; cases heq
      split at h
      · rename_i a heq2
        have hdf : Engine.P.sdoDefault sd = some a := by
          cases hdf : Engine.P.sdoDefault sd with
          | none => rw [hdf] at heq2; cases heq2
          | some a' =>
            rw [hdf] at heq2
            simp only [Option.filter] at heq2
            split at heq2
            · cases heq2; rfl
            · cases heq2
        simp only [Contains.dfltShape] at h
        split at h
        · rename_i heq3
          have ha := contains_algId_eq heq3
          subst ha
          exact contains_at_dflt H chk st fr sd nd v hsd b hrow hdf fun s' fs' =>
            contains_dflt_steps H chk s' fs' nd v sym hv _ ih b T hTt h
        · cases h
      · rename_i heq2
        have hnd : (Engine.P.sdoDefault sd).bind Engine.P.alg = none := by
          cases hdf : Engine.P.sdoDefault sd with
          | none => rfl
          | some a' =>
            rw [hdf] at heq2
            simp only [Option.filter] at heq2
            split at heq2
            · cases heq2
            · rename_i hal
              cases hx : Engine.P.alg a' with
              | none => exact hx
              | some g => rw [hx] at hal; exact absurd rfl hal
        split at h
        · rename_i k hk
          split at h
          · rename_i c hch
            exact contains_at_chain H chk st fr sd nd v hsd b k c hrow hnd hk hch (ih sd c b h)
          · cases h
        · cases h

/-- The engine's shortcut at Contains and ComputedPropertyContains is the specification's steps, given the
program's rows (`ContainsRows`). -/
theorem contains_sdoRow_of [PinsHold] (H : Host F) (chk : Bool) (hrows : ContainsRows) (sd : SdoId) :
    SdoRowOk (Ctx.spec Engine.P' H chk) sd
      (Contains.accelSdo (Engine.Machine.facts Engine.P'.P).tab sd) := by
  intro c nd vs r hc he
  rw [show Engine.P'.P = Engine.P from rfl] at he
  unfold Contains.accelSdo at he
  split at he
  · rename_i v
    cases hs : Contains.symOf v with
    | none => rw [hs] at he; cases he
    | some sym =>
      rw [hs] at he
      simp only [Option.bind_some] at he
      cases hw : Contains.walk (Engine.Machine.facts Engine.P).tab sym Contains.depthMax sd nd with
      | none => rw [hw] at he; cases he
      | some b =>
        rw [hw] at he
        cases he
        obtain ⟨s, fr, ctl⟩ := c
        cases hc
        refine contains_walk H chk hrows v sym hs _ (fun _ _ => ?_) (fun _ => ?_) ?_ ?_
          Contains.depthMax sd nd b hw s fr
        all_goals simp only [Engine.Machine.facts, Engine.Accel.Contains.tabOf]
  · cases he


/-! ## The program's rows, from a check of its row table -/

set_option maxRecDepth 8000 in
/-- A production an SDO has a row at is a key of the source's row table. -/
theorem contains_row_key (s : SdoId) (k : ProdId) (r : Ecma.SdoRow) (h : Engine.P.row s k = some r) :
    (s, k) ∈ Spec.src.rowMap.keys := by
  rw [Engine.P_eq] at h
  dsimp only [Src.expanded, Src.prog, Src.index] at h
  generalize ho : Spec.src.rowMap[(s, k)]? = o at h
  cases o with
  | none => cases h
  | some r0 =>
    rw [Std.HashMap.mem_keys, Std.HashMap.mem_iff_isSome_getElem?, ho]
    rfl

/-- The program's rows are as the walk needs, where the check of the row table holds. -/
theorem containsRows_of_check (h : containsRowsCheck = true) : ContainsRows := by
  intro s k r n code hs hrow hlook
  have hk := contains_row_key s k r hrow
  have := List.all_eq_true.mp h (s, k) hk
  have hs' : (s == Known.sdoContains || s == Known.sdoComputedPropertyContains) = true := by rcases hs with rfl | rfl <;> rfl
  simp only [hs', Bool.not_true, Bool.false_or, hrow, hlook, Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1, Code.optEqB_sound _ _ this.2⟩

/-- Contains' and ComputedPropertyContains' rows of the table: the engine's shortcut is the specification's
steps, where the check of the program's row table holds. -/
theorem contains_sdoRow [PinsHold] (H : Host F) (chk : Bool) (hcheck : containsRowsCheck = true) :
    SdoRowOk (Ctx.spec Engine.P' H chk) Known.sdoContains (Contains.accelSdo (Engine.Machine.facts Engine.P'.P).tab Known.sdoContains) ∧
    SdoRowOk (Ctx.spec Engine.P' H chk) Known.sdoComputedPropertyContains (Contains.accelSdo (Engine.Machine.facts Engine.P'.P).tab Known.sdoComputedPropertyContains) :=
  ⟨contains_sdoRow_of H chk (containsRows_of_check hcheck) Known.sdoContains,
    contains_sdoRow_of H chk (containsRows_of_check hcheck) Known.sdoComputedPropertyContains⟩

end Engine.Machine
