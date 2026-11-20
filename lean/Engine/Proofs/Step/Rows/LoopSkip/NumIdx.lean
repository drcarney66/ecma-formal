module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Num
public import Engine.Proofs.Radix

@[expose] public section

/-!
# `Number::toString` for non-negative integer keys below `2^53`

Minimal symbolic execution of `Number::toString(x, 10)` needed by `LoopSkip/Round.lean` when `x = 𝔽(i)` for
an integer `0 ≤ i < 2^53`:
* `i = 0`: stops at step 2 with `"0"`.
* `0 < i < 2^53`: step 5 (`n, k, s`) satisfies `-5 ≤ n ≤ 21` and `n ≥ k`, taking only branch 6.a.i.
Replaces `Rows/ToString.lean` using 6 pinned algorithms (12 pins).
-/

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

variable (H : Host F) (rd : ErratumId → Reading) (chk : Bool)

macro "ts_osteps" : tactic => `(tactic| repeat (
  (fail_if_success (show Steps _ ⟨_, _, .op _⟩ _))
  (fail_if_success (show Steps _ ⟨_, _, .loop .round _⟩ _))
  gstep))

macro "ts_psteps" : tactic => `(tactic| repeat ((fail_if_success (show Steps _ ⟨_, _, .invoke _⟩ _)); mstep))
macro "ts_prim_unfold" : tactic => `(tactic| (unfold primOn; simp (config := { decide := true }) only [↓reduceIte]))
macro "ts_enter_alg " g:term:max c:term:max : tactic => `(tactic| refine Steps.next (step_alg _ _ _ _ _ _ _ _ _ $g $c) ?_)

theorem ts_step_leaf (X : Ctx F) (s s' : State F) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F)) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (k : Leaf) (done : List (Val F))
    (v w : Val F) (h : leaf (leafCtx X) k (v :: done).reverse s = .ok w s') :
    step X ⟨s, ⟨a, nd, sl, kd, p, .args (.leaf k) done [] :: K, ci⟩ :: fs, .val v⟩ =
      .inl ⟨s', ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val w⟩ := by
  have e : step X ⟨s, ⟨a, nd, sl, kd, p, .args (.leaf k) done [] :: K, ci⟩ :: fs, .val v⟩ =
      leafV ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val v⟩ (leaf (leafCtx X) k (v :: done).reverse) := rfl
  rw [e]; simp only [leafV, bindR, h]; rfl

def TsEv (X : Ctx F) (sl : Array (Val F)) (o : Op) (v : Val F) : Prop :=
  ∀ (s : State F) (a : AlgId) (nd : Option F.Node) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat)
    (fs : List (Frame F)),
    Steps X ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .op o⟩ ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val v⟩

inductive TsEvL (X : Ctx F) (sl : Array (Val F)) : List Op → List (Val F) → Prop
  | nil : TsEvL X sl [] []
  | cons {o : Op} {v : Val F} {os : List Op} {vs : List (Val F)} : TsEv X sl o v → TsEvL X sl os vs →
    TsEvL X sl (o :: os) (v :: vs)

def TsCall (X : Ctx F) (a : AlgId) (vs : List (Val F)) (w : Val F) : Prop :=
  ∀ (s : State F) (fr : List (Frame F)), Steps X ⟨s, fr, .invoke (.alg a vs)⟩ ⟨s, fr, .val w⟩

theorem TsEvL.steps {X : Ctx F} {sl : Array (Val F)} {os : List Op} {vs : List (Val F)} (h : TsEvL X sl os vs) :
    ∀ (o : Op) (v : Val F) (done : List (Val F)), TsEv X sl o v → ∀ (s : State F) (a : AlgId) (nd : Option F.Node)
      (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (f : Fin F),
      ∃ vl done', (vl :: done').reverse = done.reverse ++ v :: vs ∧
        Steps X ⟨s, ⟨a, nd, sl, kd, p, .args f done os :: K, ci⟩ :: fs, .op o⟩
          ⟨s, ⟨a, nd, sl, kd, p, .args f done' [] :: K, ci⟩ :: fs, .val vl⟩ := by
  induction h with
  | nil => intro o v done ho s a nd kd p K ci fs f; exact ⟨v, done, by simp, ho _ _ _ _ _ _ _ _⟩
  | cons ho' _ ih =>
    intro o v done ho s a nd kd p K ci fs f
    obtain ⟨vl, done', e, st⟩ := ih _ _ (v :: done) ho' s a nd kd p K ci fs f
    refine ⟨vl, done', by simpa using e, Steps.trans (ho _ _ _ _ _ _ _ _) (by mstep; exact st)⟩

namespace TsEv
variable {X : Ctx F} {sl : Array (Val F)}

theorem var {x : Slot} {w : Val F} (h : sl.getD x .unbound = w) (hw : w ≠ .unbound) : TsEv X sl (.var x) w :=
  fun s a nd kd p K ci fs => Steps.next (step_var X s ⟨a, nd, sl, kd, p, K, ci⟩ fs x w h hw) (.refl _)

theorem const {k : Const} {w : Val F} (h : constV (M := F) k = Run.pure w) : TsEv X sl (.const k) w := by
  intro s a nd kd p K ci fs
  have e : step X ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .op (.const k)⟩ =
      leafV ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .op (.const k)⟩ (constV k) := rfl
  rw [h] at e; exact Steps.next e (.refl _)

theorem bnd {x : Slot} {w : Val F} (h : (sl.getD x .unbound).binder = w) : TsEv X sl (.bnd x) w := by
  intro s a nd kd p K ci fs; subst h; mstep; exact .refl _

theorem cast {o : Op} {v w : Val F} (h : v = w) (e : TsEv X sl o v) : TsEv X sl o w := h ▸ e

theorem leaf2 {k : Leaf} {a b : Op} {va vb w : Val F} (ha : TsEv X sl a va) (hb : TsEv X sl b vb)
    (h : ∀ s, leaf (leafCtx X) k [va, vb] s = .ok w s) : TsEv X sl (.leaf k [a, b]) w := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (ha _ _ _ _ _ _ _ _) ?_; mstep; refine Steps.trans (hb _ _ _ _ _ _ _ _) ?_
  exact Steps.next (ts_step_leaf X s s _ _ _ _ _ _ _ _ k [va] vb w (h s)) (.refl _)

theorem prim {q : PrimId} {o : Op} {os : List Op} {v w : Val F} {vs : List (Val F)}
    (h : TsEvL X sl (o :: os) (v :: vs)) (hq : plainPrim q = true)
    (hp : progPrim (leafCtx X) X.P X.H q (v :: vs) = none) (hr : ∀ s, Ecma.prim q (v :: vs) s = .ok w s) :
    TsEv X sl (.call (.prim q) (o :: os)) w := by
  intro s a nd kd p K ci fs
  cases h with | cons ho hl =>
    obtain ⟨vl, done', e, st⟩ := hl.steps o v [] ho s a nd kd p K ci fs (.call (.prim q))
    have e' : (vl :: done').reverse = v :: vs := by simpa using e
    mstep; refine Steps.trans st ?_
    refine Steps.next (c' := ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.prim q (vl :: done').reverse)⟩) rfl ?_
    rw [e']; exact Steps.next (step_prim_ok X s s _ q (v :: vs) w hq hp (hr s)) (.refl _)

theorem prim1 {q : PrimId} {a : Op} {va w : Val F} (ha : TsEv X sl a va) (hq : plainPrim q = true)
    (hp : progPrim (leafCtx X) X.P X.H q [va] = none) (h : ∀ s, Ecma.prim q [va] s = .ok w s) :
    TsEv X sl (.call (.prim q) [a]) w := prim (.cons ha .nil) hq hp h

theorem alg {g : AlgId} {o : Op} {os : List Op} {v w : Val F} {vs : List (Val F)}
    (h : TsEvL X sl (o :: os) (v :: vs)) (hc : TsCall X g (v :: vs) w) : TsEv X sl (.call (.alg g) (o :: os)) w := by
  intro s a nd kd p K ci fs
  cases h with | cons ho hl =>
    obtain ⟨vl, done', e, st⟩ := hl.steps o v [] ho s a nd kd p K ci fs (.call (.alg g))
    have e' : (vl :: done').reverse = v :: vs := by simpa using e
    mstep; refine Steps.trans st ?_
    refine Steps.next (c' := ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .invoke (.alg g (vl :: done').reverse)⟩) rfl ?_
    rw [e']; exact hc _ _

theorem is1 {neg nei : Bool} {a b : Op} {va vb : Val F} {r : Bool} (ha : TsEv X sl a va) (hb : TsEv X sl b vb)
    (h : ∀ s, leaf (leafCtx X) (.isVal neg nei) [va, vb] s = .ok (.bool r) s) :
    TsEv X sl (a.bind (.and [.leaf (.isVal neg nei) [.bound, b]])) (.bool r) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (ha _ _ _ _ _ _ _ _) ?_; iterate 5 mstep
  refine Steps.trans (hb _ _ _ _ _ _ _ _) ?_
  refine Steps.next (ts_step_leaf X s s _ _ _ _ _ _ _ _ _ [va] vb _ (h s)) ?_
  cases r <;> (mstep; mstep; exact .refl _)

theorem is2 {neg nei : Bool} {a b c : Op} {va vb vc : Val F} {r : Bool} (ha : TsEv X sl a va) (hb : TsEv X sl b vb)
    (hc : TsEv X sl c vc) (h : ∀ s, leaf (leafCtx X) (.isVal neg nei) [va, vb, vc] s = .ok (.bool r) s) :
    TsEv X sl (a.bind (.and [.leaf (.isVal neg nei) [.bound, b, c]])) (.bool r) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (ha _ _ _ _ _ _ _ _) ?_; iterate 5 mstep
  refine Steps.trans (hb _ _ _ _ _ _ _ _) ?_; mstep; refine Steps.trans (hc _ _ _ _ _ _ _ _) ?_
  refine Steps.next (ts_step_leaf X s s _ _ _ _ _ _ _ _ _ [vb, va] vc _ (h s)) ?_
  cases r <;> (mstep; mstep; exact .refl _)

theorem bin {o : BinOp} {a b : Op} {x y z : Model.MathVal} (ha : TsEv X sl a (.math x)) (hb : TsEv X sl b (.math y))
    (h : op? o x y = some z) : TsEv X sl (.leaf (.bin o) [a, b]) (.math z) :=
  leaf2 ha hb fun s => by show (binOp o (.math x) (.math y) : Run F (Val F)) s = _; unfold op? at h; simp only [binOp, h]; rfl

theorem lt {a b : Op} {x y : Model.MathVal} {r : Bool} (ha : TsEv X sl a (.math x)) (hb : TsEv X sl b (.math y))
    (h : lt? x y = some r) : TsEv X sl (.leaf (.rel .lt) [a, b]) (.bool r) :=
  leaf2 ha hb fun _ => by
    cases h; show (do return Val.bool (← relOp .lt (.math x) (.math y)) : Run F (Val F)) _ = _
    simp only [bind, Run.bind, relOp, relOp.lt, Run.Res.bind]; rfl

theorem ge {a b : Op} {x y : Model.MathVal} {r : Bool} (ha : TsEv X sl a (.math x)) (hb : TsEv X sl b (.math y))
    (h : ge? x y = some r) : TsEv X sl (.leaf (.rel .ge) [a, b]) (.bool r) :=
  leaf2 ha hb fun _ => by
    simp only [ge?, lt?, eq?, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, _, h2, h3⟩ := h; cases Option.some.inj h3; cases h1; cases h2
    show (do return Val.bool (← relOp .ge (.math x) (.math y)) : Run F (Val F)) _ = _
    simp only [bind, Run.bind, relOp, relOp.lt, relOp.eq, Run.Res.bind]; rfl

theorem ne {a b : Op} {x y : Model.MathVal} {r : Bool} (ha : TsEv X sl a (.math x)) (hb : TsEv X sl b (.math y))
    (h : ne? x y = some r) : TsEv X sl (.leaf (.rel .ne) [a, b]) (.bool r) :=
  leaf2 ha hb fun _ => by
    simp only [ne?, eq?, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h3⟩ := h; cases Option.some.inj h3; cases h1
    show (do return Val.bool (← relOp .ne (.math x) (.math y)) : Run F (Val F)) _ = _
    simp only [bind, Run.bind, relOp, relOp.eq, Run.Res.bind]; rfl

theorem or2 {a b : Op} {c d : Bool} (ha : TsEv X sl a (.bool c)) (hb : c = false → TsEv X sl b (.bool d)) :
    TsEv X sl (.or [a, b]) (.bool (c || d)) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (ha _ _ _ _ _ _ _ _) ?_
  cases c
  · mstep; refine Steps.trans (hb rfl _ _ _ _ _ _ _ _) ?_; cases d <;> (mstep; exact .refl _)
  · mstep; exact .refl _

theorem and3 {a b c : Op} {r : Bool} (ha : TsEv X sl a (.bool true)) (hb : TsEv X sl b (.bool true))
    (hc : TsEv X sl c (.bool r)) : TsEv X sl (.and [a, b, c]) (.bool r) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (ha _ _ _ _ _ _ _ _) ?_; mstep; refine Steps.trans (hb _ _ _ _ _ _ _ _) ?_
  mstep; refine Steps.trans (hc _ _ _ _ _ _ _ _) ?_; cases r <;> (mstep; exact .refl _)

theorem steps {X : Ctx F} {sl : Array (Val F)} {o : Op} {v : Val F} (h : TsEv X sl o v) {s : State F} {a : AlgId}
    {nd : Option F.Node} {kd : Kind} {p : List Nat} {K : List (Kont F)} {ci : Option Nat} {fs : List (Frame F)}
    {d : Cfg F} (k : Steps X ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val v⟩ d) :
    Steps X ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .op o⟩ d := Steps.trans (h _ _ _ _ _ _ _ _) k

end TsEv

macro "ts_ev_var" : term => `(TsEv.var (by rfl) (by simp))
macro "ts_ev_bnd" : term => `(TsEv.bnd (by rfl))
macro "ts_ev " t:term : tactic => `(tactic| refine TsEv.steps $t ?_)

theorem ts_assert {sl : Array (Val F)} {cd : Op} (hcd : TsEv (Ctx.spec Engine.P' H rd chk) sl cd (.bool true))
    (s : State F) (a : AlgId) (nd : Option F.Node) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat)
    (fs : List (Frame F)) (i : Ins) (is : Code) :
    Steps (Ctx.spec Engine.P' H rd chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .code (.assert cd :: i :: is)⟩
      ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .code (i :: is)⟩ := by
  cases chk
  · mstep; mstep; exact .refl _
  · mstep; refine Steps.trans (hcd _ _ _ _ _ _ _ _) ?_; mstep; mstep; exact .refl _

/-! ## Primitives, sorts, and step 5 -/

abbrev tsSl (x : F.Num) (r : Model.MathVal) (v2 v3 v4 v5 : Val F) : Array (Val F) := #[.num x, .math r, v2, v3, v4, v5]
abbrev tsSlots (x : F.Num) (r : Model.MathVal) : Array (Val F) := tsSl x r .unbound .unbound .unbound .unbound
def tsReading : Code := match toStringCode[9]? with | some (Ins.reading _ c) => c | _ => []
def tsRest : Code := toStringCode.drop 10
def tsFixedCode : Code := match tsRest[1]? with | some (Ins.br _ c _) => c | _ => []
theorem ts_zero {X : Ctx F} {sl : Array (Val F)} : TsEv X sl (.const (.math .none (.num (.dec 0)))) (.math (F.ofNat 0)) := TsEv.const rfl
theorem ts_one {X : Ctx F} {sl : Array (Val F)} : TsEv X sl (.const (.math .none (.num (.dec 1)))) (.math Engine.Accel.one) := TsEv.const rfl
theorem ts_op_add (x y : Model.MathVal) : op? .add x y = some (F.add x y) := rfl
theorem ts_op_sub (x y : Model.MathVal) : op? .sub x y = some (F.sub x y) := rfl
private theorem ts_isNum {X : Ctx F} (x y : F.Num) (s : State F) :
    leaf (leafCtx X) (.isVal false false) [.num y, .num x] s = .ok (.bool (Val.same (M := F) (.num y) (.num x))) s := by
  simp [leaf, isVals, sameIs, Val.incomparable, bind, Run.bind, Run.Res.bind, Run.pure, pure, Val.used]
private theorem ts_isNum2 {X : Ctx F} (x y z : F.Num) (s : State F) :
    leaf (leafCtx X) (.isVal false false) [.num x, .num y, .num z] s =
      .ok (.bool (Val.same (M := F) (.num x) (.num y) || Val.same (M := F) (.num x) (.num z))) s := by
  simp [leaf, isVals, sameIs, Val.incomparable, bind, Run.bind, Run.Res.bind, Run.pure, pure, Val.used]
def tsSameView : NumView Model.MathVal → NumView Model.MathVal → Bool
  | .nan, .nan | .posInf, .posInf | .negInf, .negInf | .posZero, .posZero | .negZero, .negZero => true
  | .finite a, .finite b => F.eq a b | _, _ => false
theorem ts_sameView (x y : F.Num) :
    Val.same (M := F) (.num x) (.num y) = tsSameView (F.numView x) (F.numView y) := by
  simp only [Val.same]; show _ = tsSameView (Model.numView x.val) (Model.numView y.val)
  generalize Model.numView x.val = vx; generalize Model.numView y.val = vy; cases vx <;> cases vy <;> rfl

private theorem ts_strOfUnits_run {vs : List (Val F)} {t : F.Str} (h : cat? vs = some t) (s : State F) :
    Prims.Strings.strOfUnits (M := F) vs s = .ok (.str t) s := by
  have e : ∀ (f g : Option F.Str → Val F → Option F.Str), (∀ a v, f a v = g a v) →
      List.foldl f (some (F.strLit "")) vs = List.foldl g (some (F.strLit "")) vs := fun f g hfg => by
    rw [show f = g from funext fun a => funext fun v => hfg a v]
  unfold cat? at h; unfold Prims.Strings.strOfUnits; generalize hg : List.foldl _ _ vs = o
  have ho : o = some t := hg.symm.trans ((e _ _ fun a v => by cases a <;> cases v <;> rfl).trans h); subst ho; rfl

private theorem ts_cat_prim {q : PrimId} (hq : q = 14 ∨ q = 48) {vs : List (Val F)} {t : F.Str}
    (hu : vs.map Val.used = vs) (h : cat? vs = some t) (s : State F) : Ecma.prim q vs s = .ok (.str t) s := by
  rcases hq with rfl | rfl <;> (rw [prim_used _ _ rfl, hu]; ts_prim_unfold; exact ts_strOfUnits_run h s)

private theorem ts_interval {lo hi n : Model.MathVal} {b : Bool} (h : inInt? lo hi n = some b) (s : State F) :
    Ecma.prim 85 [.math lo, .math hi, .math n] s = .ok (.bool b) s := by
  show primOn (M := F) 85 [.math lo, .math hi, .math n] s = _; ts_prim_unfold
  show Prims.Numbers.inInterval (M := F) [.math lo, .math hi, .math n] s = _
  simp only [inInt?, le?, lt?, eq?, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, ⟨_, h1, _, h2, h3⟩, _, ⟨_, h4, _, h5, h6⟩, h7⟩ := h
  cases Option.some.inj h3; cases Option.some.inj h6; cases Option.some.inj h7
  cases h1; cases h2; cases h4; cases h5; rfl

set_option maxRecDepth 8000 in
private theorem ts_sortDef_5 : Engine.P.sortDef 5 = none := by rw [sortDef_eq]; rfl

private theorem ts_digits (i : Nat) {x : F.Num} {r m : Model.MathVal} (hx : F.numView x = .finite m)
    (hc : step5Ok r m = true) (s : State F) :
    Prims.Numbers.numberDigits (M := F) i [.num x, .math r] s =
      .ok (.math (if i == 0 then (step5 r x).1 else if i == 1 then (step5 r x).2.1 else (step5 r x).2.2)) s := by
  simp only [step5Ok] at hc
  simp only [Prims.Numbers.numberDigits, show Model.numView x.val = _ from hx, hc, ↓reduceIte, step5]; rfl

set_option maxRecDepth 8000 in
theorem ts_step5 (x : F.Num) (r m : Model.MathVal) (hx : F.numView x = .finite m) (hc : step5Ok r m = true)
    (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) (K : List (Kont F)) (q : List Nat)
    (v2 v3 v4 v5 : Val F) :
    Steps (Ctx.spec Engine.P' H rd chk)
      ⟨st, ⟨a, nd, tsSl x r v2 v3 v4 v5, .steps false true true, q, K, none⟩ :: fs, .code tsReading⟩
      ⟨st, ⟨a, nd, tsSl x r (.math (step5 r x).1) (.math (step5 r x).2.1) (.math (step5 r x).2.2) v5,
        .steps false true true, [3, 196, 0, 5], K, none⟩ :: fs, .done⟩ := by
  ts_osteps
  ts_ev TsEv.prim (.cons ts_ev_var (.cons ts_ev_var .nil)) rfl rfl (fun s => by
    show primOn (M := F) 292 _ s = _; ts_prim_unfold; exact ts_digits 0 hx hc s)
  ts_osteps
  ts_ev TsEv.prim (.cons ts_ev_var (.cons ts_ev_var .nil)) rfl rfl (fun s => by
    show primOn (M := F) 293 _ s = _; ts_prim_unfold; exact ts_digits 1 hx hc s)
  ts_osteps
  ts_ev TsEv.prim (.cons ts_ev_var (.cons ts_ev_var .nil)) rfl rfl (fun s => by
    show primOn (M := F) 294 _ s = _; ts_prim_unfold; exact ts_digits 2 hx hc s)
  ts_osteps; exact .refl _

/-! ## Overlay phrase helpers (6 algorithms) -/

theorem ts_units [PinsHold] (t : F.Str) : TsCall (Ctx.spec Engine.P' H rd chk) ⟨2641, 0⟩ [.str t] (.str t) := by
  intro s fr; ts_enter_alg tsUnitsAlg_pin tsUnitsCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.str t], .steps false true true, [], [], none⟩ :: _, .code tsUnitsCode⟩ _
  gsteps; exact .refl _

theorem ts_strOf [PinsHold] (c : Model.MathVal) (t : F.Str) (h : cat? [.math c] = some t) :
    TsCall (Ctx.spec Engine.P' H rd chk) ⟨2671, 0⟩ [.math c] (.str t) := by
  intro s fr; ts_enter_alg tsStrOfAlg_pin tsStrOfCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.math c], .steps false true true, [], [], none⟩ :: _, .code tsStrOfCode⟩ _
  ts_osteps; ts_ev TsEv.prim (.cons ts_ev_var .nil) rfl rfl (ts_cat_prim (.inr rfl) rfl h); gsteps; exact .refl _

theorem ts_kDigits [PinsHold] (k : Model.MathVal) (t u : F.Str) (h : kDigits? k t = some u) :
    TsCall (Ctx.spec Engine.P' H rd chk) ⟨2637, 0⟩ [.math k, .str t] (.str u) := by
  simp only [kDigits?, bind, Option.bind_eq_some_iff, guard] at h
  obtain ⟨_, h1, h2⟩ := h; cases Option.some.inj h2; split at h1
  · rename_i hk; intro s fr; ts_enter_alg tsKDigitsAlg_pin tsKDigitsCode_pin
    show Steps _ ⟨s, ⟨_, none, #[.math k, .str t], .steps false true true, [], [], none⟩ :: _, .code tsKDigitsCode⟩ _
    mstep
    refine Steps.trans (ts_assert H rd chk (TsEv.cast (congrArg Val.bool hk) <|
      TsEv.is1 (TsEv.prim (.cons ts_ev_bnd .nil) rfl rfl fun _ => by
        show primOn (M := F) 50 [.str t] _ = _; ts_prim_unfold; rfl)
      ts_ev_var (fun _ => by
        simp [leaf, isVals, sameIs, Val.incomparable, bind, Run.bind, Run.Res.bind, Run.pure, pure, Val.used, Val.same]))
      _ _ _ _ _ _ _ _ _ _) ?_
    gsteps; exact .refl _
  · cases h1

private theorem ts_sort9Ok {sl : Array (Val F)} {z : Int} (hn : sl.getD 0 .unbound = .math (.int z)) :
    TsEv (Ctx.spec Engine.P' H rd chk) sl ((Op.var 0).bind (.and [.leaf (.isTy false false)
      [(Op.leaf .used [.bound]).bind (.or [.call (.sort 9) [.bound]])]])) (.bool true) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (TsEv.var hn (by simp) _ _ _ _ _ _ _ _) ?_; ts_psteps
  refine Steps.next (step_sort_int H rd chk s _ z) ?_; gsteps; exact .refl _

private theorem ts_radixOk {sl : Array (Val F)} {r : Model.MathVal} (hr : sl.getD 1 .unbound = .math r)
    (h : inInt? (F.ofNat 2) (F.ofNat 36) r = some true) :
    TsEv (Ctx.spec Engine.P' H rd chk) sl ((Op.var 1).bind (.and [.leaf (.isTy false false)
      [.call (.prim 85) [.const (.math .none (.num (.dec 2))), .const (.math .none (.num (.dec 36))), .bound]]]))
      (.bool true) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (TsEv.var hr (by simp) _ _ _ _ _ _ _ _) ?_; ts_psteps
  mprim (ts_interval h _); gsteps; exact .refl _

theorem ts_repr_int [PinsHold] (n r : Nat) (hr2 : 2 ≤ r) (hr36 : r ≤ 36) :
    TsCall (Ctx.spec Engine.P' H rd chk) ⟨2633, 0⟩ [.math (.int n), .math (.int r)]
      (.str (F.intToRadix (.int n) (.int r))) := by
  have hb1 : ge? (.int (n : Int)) (F.ofNat 0) = some true := by
    show some (decide ((0 : Int) < n) || (n : Int) == 0) = some true; rcases n with _ | n <;> simp
  have hb2 : inInt? (F.ofNat 2) (F.ofNat 36) (.int (r : Int)) = some true := by
    show some ((decide ((2 : Int) < r) || ((2 : Int) == r)) && (decide ((r : Int) < 36) || ((r : Int) == 36))) = _
    congr 1; simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  intro s fr; ts_enter_alg tsReprAlg_pin tsReprCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.math (.int n), .math (.int r)], .steps false true true, [], [], none⟩ :: _,
    .code tsReprCode⟩ _
  gsteps
  refine Steps.next (by simp only [step, invoke, spec_P, ts_sortDef_5, sortTest]; rfl :
    step (Ctx.spec Engine.P' H rd chk) _ = .inl _) ?_; gsteps
  refine Steps.trans (ts_assert H rd chk
    (TsEv.and3 (ts_sort9Ok H rd chk rfl) (TsEv.ge ts_ev_var ts_zero hb1) (ts_radixOk H rd chk rfl hb2))
    _ _ _ _ _ _ _ _ _ _) ?_
  ts_osteps
  ts_ev (TsEv.prim (w := .str (F.intToRadix (.int n) (.int r))) (.cons ts_ev_var (.cons ts_ev_var .nil)) rfl rfl fun st => by
    show primOn (M := F) 305 [.math (.int n), .math (.int r)] st = _; ts_prim_unfold
    show (if F.isInt (.int n) && !F.lt (.int n) (.int 0) && F.isInt (.int r) && !F.lt (.int r) (.int 2) &&
      !F.lt (.int 36) (.int r) then Run.pure (Val.str (F.intToRadix (.int n) (.int r))) else Run.stop .sortError) st = _
    split
    · rfl
    · next hf =>
      exfalso; apply hf; simp only [Model.MathVal.isInt, Model.MathVal.lt, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨⟨⟨⟨trivial, decide_eq_false (by omega)⟩, trivial⟩, decide_eq_false (by omega)⟩, decide_eq_false (by omega)⟩)
  gsteps; exact .refl _

theorem ts_occ_nat [PinsHold] (n : Nat) (c : Model.MathVal) (cs : F.Str) (hcs : cat? [.math c] = some cs) :
    TsCall (Ctx.spec Engine.P' H rd chk) ⟨2700, 0⟩ [.math (.int n), .math c] (.str (F.strRepeat (.int n) cs)) := by
  intro s fr; ts_enter_alg tsOccAlg_pin tsOccCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.math (.int n), .math c], .steps false true true, [], [], none⟩ :: _, .code tsOccCode⟩ _
  ts_osteps
  ts_ev (TsEv.prim (w := .str (F.strRepeat (.int n) cs))
    (.cons (TsEv.alg (.cons ts_ev_bnd .nil) (ts_strOf H rd chk c cs hcs)) (.cons ts_ev_var .nil)) rfl rfl fun st => by
      show primOn (M := F) 289 [.str cs, .math (.int n)] st = _; ts_prim_unfold
      show Prims.Strings.stringRepeat (M := F) [.str cs, .math (.int n)] st = _
      unfold Prims.Strings.stringRepeat; dsimp only; split
      · next hf => exfalso; rcases hf with hf | hf <;> (simp only [Model.MathVal.isInt, Model.MathVal.lt] at hf; omega)
      · rfl)
  gsteps; exact .refl _

/-! ## `Number::toString` on `0` and positive integers `< 2^53` -/

private theorem ts_isNaN (x : F.Num) (r : Model.MathVal) :
    TsEv (Ctx.spec Engine.P' H rd chk) (tsSlots x r) ((Op.var 0).bind (.and [.leaf (.isVal false false)
      [.bound, .const (.val (.nan .none))]])) (.bool (Val.same (M := F) (.num x) (.num F.numNaN))) :=
  TsEv.is1 ts_ev_var (TsEv.const rfl) (ts_isNum _ _)

private theorem ts_isZero (x : F.Num) (r : Model.MathVal) :
    TsEv (Ctx.spec Engine.P' H rd chk) (tsSlots x r) ((Op.var 0).bind (.and [.leaf (.isVal false false)
      [.bound, .const (.val (.num .plus (.num (.dec 0)) .f)), .const (.val (.num .minus (.num (.dec 0)) .f))]]))
      (.bool (Val.same (M := F) (.num x) (.num (F.numZero false)) || Val.same (M := F) (.num x) (.num (F.numZero true)))) :=
  TsEv.is2 ts_ev_var (TsEv.const rfl) (TsEv.const rfl) (ts_isNum2 _ _ _)

private theorem ts_isNeg (x : F.Num) (r : Model.MathVal) :
    TsEv (Ctx.spec Engine.P' H rd chk) (tsSlots x r) (.leaf (.rel .lt)
      [.var 0, .const (.val (.num .minus (.num (.dec 0)) .f))]) (.bool (F.numLt x (F.numZero true))) :=
  TsEv.leaf2 ts_ev_var (TsEv.const rfl) fun _ => rfl

private theorem ts_isInf (x : F.Num) (r : Model.MathVal) :
    TsEv (Ctx.spec Engine.P' H rd chk) (tsSlots x r) ((Op.var 0).bind (.and [.leaf (.isVal false false)
      [.bound, .const (.val (.num .plus .inf .f))]])) (.bool (Val.same (M := F) (.num x) (.num (F.numInf false)))) :=
  TsEv.is1 ts_ev_var (TsEv.const rfl) (ts_isNum _ _)

theorem numIdx_zero (r : Model.MathVal) (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) :
    Steps (Ctx.spec Engine.P' H rd chk)
      ⟨st, ⟨a, nd, tsSlots (F.numZero false) r, .steps false true true, [], [], none⟩ :: fs, .code toStringCode⟩
      ⟨st, fs, .val (.str (F.strLit "0"))⟩ := by
  have eNaN := ts_sameView (F.numZero false) F.numNaN
  have ePz := ts_sameView (F.numZero false) (F.numZero false)
  have eNz := ts_sameView (F.numZero false) (F.numZero true)
  rw [Engine.Impl.numView_nan] at eNaN; rw [Engine.Impl.numView_zero] at ePz eNz
  ts_osteps; ts_ev ts_isNaN H rd chk (F.numZero false) r; rw [eNaN]
  ts_osteps; ts_ev ts_isZero H rd chk (F.numZero false) r; rw [ePz, eNz]
  gsteps; exact .refl _

private theorem ts_expOk {sl : Array (Val F)} {n : Model.MathVal} (hn : sl.getD 2 .unbound = .math n)
    (h : inInt? (.int (-5)) (F.ofNat 21) n = some true) :
    TsEv (Ctx.spec Engine.P' H rd chk) sl ((Op.var 2).bind (.and [.leaf (.isTy false false)
      [.call (.prim 85) [.const (.math .minus (.num (.dec 5))), .const (.math .none (.num (.dec 21))), .bound]]]))
      (.bool true) := by
  intro s a nd kd p K ci fs
  mstep; refine Steps.trans (TsEv.var hn (by simp) _ _ _ _ _ _ _ _) ?_; ts_psteps
  mprim (ts_interval h _); gsteps; exact .refl _

private theorem ts_reading (s : State F) (a : AlgId) (nd : Option F.Node)
    (sl : Array (Val F)) (kd : Kind) (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (code : Code) (i : Ins) (is : Code) :
    step (Ctx.spec Engine.P' H rd chk) ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .code (Ins.reading 196 code :: i :: is)⟩ =
      .inl ⟨s, ⟨a, nd, sl, kd, p, .seq (i :: is) :: K, ci⟩ :: fs, .code code⟩ := rfl

set_option maxRecDepth 8000 in
/-- `Number::toString(x, 10)` on a finite positive `x` whose step 5 `(n, k, s)` has `1 ≤ k ≤ n ≤ 21` and `s : Nat`. -/
theorem numIdx_step [PinsHold] (x : F.Num) (m : Model.MathVal) (hv : F.numView x = .finite m)
    (hlt : F.numLt x (F.numZero true) = false) (hm0 : F.lt (F.ofNat 0) m = true)
    (n k s : Nat) (h5 : step5 (F.ofNat 10) x = (.int n, .int k, .int s)) (hn21 : n ≤ 21) (hkn : k ≤ n)
    (t : F.Str) (hkd : kDigits? (.int k) (F.intToRadix (.int s) (.int 10)) = some (F.intToRadix (.int s) (.int 10)))
    (hcat : cat? [.str (F.intToRadix (.int s) (.int 10)), .str (F.strRepeat (.int (n - k : Nat)) #[(48 : Nat).toUInt16])] = some t)
    (st : State F) (fs : List (Frame F)) (a : AlgId) (nd : Option F.Node) :
    Steps (Ctx.spec Engine.P' H rd chk)
      ⟨st, ⟨a, nd, tsSlots x (F.ofNat 10), .steps false true true, [], [], none⟩ :: fs, .code toStringCode⟩
      ⟨st, fs, .val (.str t)⟩ := by
  have eNaN := ts_sameView x F.numNaN; have ePz := ts_sameView x (F.numZero false)
  have eNz := ts_sameView x (F.numZero true); have eInf := ts_sameView x (F.numInf false)
  rw [Engine.Impl.numView_nan] at eNaN; rw [Engine.Impl.numView_zero] at ePz eNz; rw [Engine.Impl.numView_inf] at eInf
  have hok : step5Ok (F.ofNat 10) m = true := by
    simp only [step5Ok, Bool.and_eq_true, Bool.not_eq_true']; exact ⟨⟨⟨hm0, rfl⟩, by decide⟩, by decide⟩
  have hwin : inInt? (.int (-5)) (F.ofNat 21) (.int n) = some true := by
    show some ((decide ((-5 : Int) < n) || ((-5 : Int) == n)) && (decide ((n : Int) < 21) || ((n : Int) == 21))) = _
    congr 1; simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  have hge : ge? (.int n) (.int k) = some true := by
    show some (decide ((k : Int) < n) || ((n : Int) == k)) = _; congr 1
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]; omega
  have hsub : op? .sub (.int n) (.int k) = some (.int (n - k : Nat)) := by
    show some (Model.MathVal.int ((n : Int) + -(k : Int))) = _; congr 2; omega
  ts_osteps; ts_ev ts_isNaN H rd chk x (F.ofNat 10); rw [eNaN, hv]
  ts_osteps; ts_ev ts_isZero H rd chk x (F.ofNat 10); rw [ePz, eNz, hv]
  iterate 3 mstep
  ts_osteps; ts_ev ts_isNeg H rd chk x (F.ofNat 10); rw [hlt]
  iterate 3 mstep
  ts_osteps; ts_ev ts_isInf H rd chk x (F.ofNat 10); rw [eInf, hv]
  ts_osteps
  refine Steps.next (ts_reading H rd chk _ _ _ _ _ _ _ _ _ _ _ _) ?_
  refine Steps.trans (ts_step5 H rd chk x (F.ofNat 10) m hv hok _ _ _ _ _ _ _ _ _ _) ?_
  rw [h5]; mstep; ts_osteps
  ts_ev TsEv.or2 (TsEv.ne ts_ev_var (TsEv.const rfl) (by rfl : ne? (F.ofNat 10) (F.ofNat 10) = some false))
    (fun _ => ts_expOk H rd chk rfl hwin)
  mstep
  show Steps _ ⟨st, ⟨a, nd, tsSl x (F.ofNat 10) (.math (.int n)) (.math (.int k)) (.math (.int s)) .unbound,
    .steps false true true, [6], [.seq _], none⟩ :: fs, .code tsFixedCode⟩ _
  ts_osteps; ts_ev TsEv.ge ts_ev_var ts_ev_var hge; ts_osteps
  ts_ev TsEv.prim (.cons (TsEv.alg (.cons (TsEv.alg (.cons ts_ev_bnd (.cons (TsEv.alg (.cons ts_ev_bnd (.cons ts_ev_bnd
    .nil)) (ts_repr_int H rd chk s 10 (by decide) (by decide))) .nil)) (ts_kDigits H rd chk _ _ _ hkd)) .nil)
    (ts_units H rd chk _))
    (.cons (TsEv.alg (.cons (TsEv.bin ts_ev_var ts_ev_var hsub)
      (.cons (TsEv.prim (.cons (TsEv.const rfl) .nil) rfl rfl fun _ => by
        show primOn (M := F) 47 [.math (F.ofNat 48)] _ = _; ts_prim_unfold
        show Prims.Strings.codeUnit (M := F) [.math (F.ofNat 48)] _ = _; rfl) .nil))
      (ts_occ_nat H rd chk _ _ #[(48 : Nat).toUInt16] (by
        unfold cat?; rw [show F.strLit "" = #[] from utf16_empty]; rfl))) .nil)) rfl rfl (ts_cat_prim (.inl rfl) rfl hcat)
  gsteps; exact .refl _

end Engine.Machine
