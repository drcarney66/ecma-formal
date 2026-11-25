module

public import Engine.Proofs.Step.Sym
public import Engine.Proofs.Step.Table
public import Engine.Proofs.Step.Rows.LoopSkip.NumIdx

@[expose] public section

namespace Engine.Machine

open Ecma Ecma.Machine Engine.Accel

variable (H : Host F) (chk : Bool)

/-! ## Sorts of a Number -/

set_option maxRecDepth 8000 in
theorem ls_sortDef_1 : Engine.P.sortDef 1 = none := by
  rw [sortDef_eq]; rfl

set_option maxRecDepth 8000 in
theorem ls_sortDef_2 : Engine.P.sortDef 2 = none := by
  rw [sortDef_eq]; rfl

set_option maxRecDepth 8000 in
theorem ls_sortDef_4 : Engine.P.sortDef 4 = none := by
  rw [sortDef_eq]; rfl

theorem ls_sort1 (s : State F) (fr : List (Frame F)) (x : F.Num) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort 1 (.num x))⟩ = .inl ⟨s, fr, .val (.bool true)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_1, sortTest]
  rfl

theorem ls_sort2 (s : State F) (fr : List (Frame F)) (x : F.Num) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort 2 (.num x))⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_2, sortTest]
  rfl

theorem ls_sort4 (s : State F) (fr : List (Frame F)) (x : F.Num) :
    step (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.sort 4 (.num x))⟩ = .inl ⟨s, fr, .val (.bool false)⟩ := by
  simp only [step, invoke, spec_P, ls_sortDef_4, sortTest]
  rfl

/-! ## ToString of a Number -/

/-- 𝔽(i) of an integer. -/
def lsNum (i : Int) : F.Num :=
  if Model.MathVal.eq (.int i) (.int 0) then F.numZero false else F.numOf (Model.MathVal.int i)

/-- The hypothesis on `Number::toString` at positive integer Numbers below `2^53` and radix `10`. -/
structure LsIntKeys : Prop where
  digits : ∀ i : Nat, 0 < i → i < 2 ^ 53 →
    numberToStr (F.ofNat 10) (F.numOf (Model.MathVal.int i)) = some (F.strLit (toString i))
  exec : ∀ i : Nat, 0 < i → i < 2 ^ 53 →
    let x := F.numOf (Model.MathVal.int i)
    ∃ (n k s : Nat),
      F.numView x = .finite (.int i) ∧
      F.numLt x (F.numZero true) = false ∧
      step5 (F.ofNat 10) x = (.int n, .int k, .int s) ∧
      n ≤ 21 ∧ k ≤ n ∧
      kDigits? (.int k) (F.intToRadix (.int s) (.int 10)) = some (F.intToRadix (.int s) (.int 10)) ∧
      cat? [.str (F.intToRadix (.int s) (.int 10)),
        .str (F.strRepeat (.int (n - k : Nat)) #[(48 : Nat).toUInt16])] = some (F.strLit (toString i))

set_option maxRecDepth 8000 in
/-- ToString(x) of a Number where Number::toString(x, 10) answers: its String, a normal completion. -/
theorem ls_toString [PinsHold] (hkeys : LsIntKeys) (i : Int) (hi0 : 0 ≤ i) (hi53 : i < 2 ^ 53)
    (t : F.Str) (h : numberToStr (F.ofNat 10) (lsNum i) = some t) (s : State F)
    (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨208, 0⟩ [.num (lsNum i)])⟩
      ⟨s, fr, .val (.comp Known.eNormal (.str t) (.enum Known.eEmpty))⟩ := by
  ts_enter_alg lsToStringAlg_pin lsToStringCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.num (lsNum i), .unbound], .steps true true true, [], [], none⟩ :: _,
    .code lsToStringCode⟩ _
  gsteps
  refine Steps.next (ls_sort2 H chk _ _ _) ?_
  gsteps
  refine Steps.next (ls_sort4 H chk _ _ _) ?_
  gsteps
  refine Steps.next (ls_sort1 H chk _ _ _) ?_
  gsteps
  refine Steps.next (step_alg H chk _ _ _ _ _ _ toStringAlg_pin toStringCode_pin) ?_
  by_cases hi : i = 0
  · subst hi
    have e0 : lsNum 0 = F.numZero false := rfl
    have h0 : numberToStr (F.ofNat 10) (F.numZero false) = some (F.strLit "0") := by
      simp only [numberToStr, fromStep1]; rfl
    rw [e0] at h ⊢
    rw [h0] at h
    cases Option.some.inj h
    refine Steps.trans (numIdx_zero H chk (F.ofNat 10) s _ toStringAlg.id none) ?_
    gsteps; exact .refl _
  · have hv0 : 0 < i.toNat := by omega
    have hv53 : i.toNat < 2 ^ 53 := by omega
    have els : lsNum i = F.numOf (.int i.toNat) := by
      have heq : (i.toNat : Int) = i := Int.toNat_of_nonneg hi0
      simp [lsNum, Model.MathVal.eq, hi, heq]
    obtain ⟨n, k, s0, hv, hlt, h5, hn21, hkn, hkd, hcat⟩ := hkeys.exec i.toNat hv0 hv53
    have hdig := hkeys.digits i.toNat hv0 hv53
    rw [els] at h ⊢
    rw [hdig] at h
    cases Option.some.inj h
    have hm0 : F.lt (F.ofNat 0) (.int i.toNat) = true := by
      show decide ((0 : Int) < i.toNat) = true
      exact decide_eq_true (by omega)
    refine Steps.trans (numIdx_step H chk (F.numOf (.int i.toNat)) (.int i.toNat) hv hlt hm0 n k s0 h5 hn21 hkn
      (F.strLit (toString i.toNat)) hkd hcat s _ toStringAlg.id none) ?_
    gsteps; exact .refl _

/-! ## The primitives -/

theorem ls_primF (i : Int) (s : State F) : Ecma.prim (M := F) 0 [.math (.int i)] s = .ok (.num (lsNum i)) s := by
  show primOn (M := F) 0 [.math (.int i)] s = _
  ts_prim_unfold
  rfl

/-- OwnPropertyHas of an object's cell. -/
theorem ls_ownHas (s : State F) (a : Nat) (t : F.Str) (sl : F.Rec (Val F)) (ps : F.Props (Val F))
    (ha : s.heap[a]? = some (.object sl ps)) :
    Ecma.prim (M := F) 102 [.obj a, .str t] s = .ok (.bool (F.propsGet ps (.inl t)).isSome) s := by
  show primOn (M := F) 102 [.obj a, .str t] s = _
  ts_prim_unfold
  simp [ownHas, objCell, readCell, ha, keyOf, bind, Run.bind, Run.Res.bind, Run.pure, pure]

/-- A read of an object's internal slot. -/
theorem ls_readSlot (s : State F) (a : Nat) (sl : F.Rec (Val F)) (ps : F.Props (Val F)) (f : FieldId) (v : Val F)
    (ha : s.heap[a]? = some (.object sl ps)) (hf : F.recGet sl f = some v) :
    readField (.obj a) f s = .ok v s := by
  have hf' : Model.WMap.get sl f = some v := hf
  simp [readField, readCell, ha, hf', bind, Run.bind, Run.Res.bind, optOr, Run.pure]

/-- The machine's transition at an internal method's receiver: the method read, its call's operands. -/
theorem ls_step_imethod (X : Ctx F) (s : State F) (a : AlgId) (nd : Option F.Node) (sl : Array (Val F)) (kd : Kind)
    (p : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (m : FieldId) (args : List Op)
    (v : Val F) (g : AlgId) (h : readField v m s = .ok (.alg g) s) :
    step X ⟨s, ⟨a, nd, sl, kd, p, .args (.recv (.imethod m) args) [] [] :: K, ci⟩ :: fs, .val v⟩ =
      startCall ⟨s, ⟨a, nd, sl, kd, p, K, ci⟩ :: fs, .val v⟩ (.alg g [v]) args := by
  simp [step, apply, finish, bindR, h]

/-! ## OrdinaryGetOwnProperty, [[GetOwnProperty]], OrdinaryGetPrototypeOf, [[GetPrototypeOf]] -/

/-- OrdinaryGetOwnProperty(O, P) of an object without the key: undefined, the state as it was. -/
theorem ls_ogop [PinsHold] (s : State F) (a : Nat) (t : F.Str) (sl : F.Rec (Val F)) (ps : F.Props (Val F))
    (ha : s.heap[a]? = some (.object sl ps)) (hk : F.propsGet ps (.inl t) = none) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨447, 0⟩ [.obj a, .str t])⟩
      ⟨s, fr, .val .undefined⟩ := by
  ts_enter_alg lsOgopAlg_pin lsOgopCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.obj a, .str t, .unbound, .unbound], .steps false true true, [], [], none⟩ :: _,
    .code lsOgopCode⟩ _
  gsteps
  mprim (ls_ownHas s a t sl ps ha)
  rw [hk]
  gsteps
  exact .refl _

/-- O.[[GetOwnProperty]](P) of an ordinary object without the key. -/
theorem ls_ordGop [PinsHold] (s : State F) (a : Nat) (t : F.Str) (sl : F.Rec (Val F)) (ps : F.Props (Val F))
    (ha : s.heap[a]? = some (.object sl ps)) (hk : F.propsGet ps (.inl t) = none) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨446, 0⟩ [.obj a, .str t])⟩
      ⟨s, fr, .val (.comp Known.eNormal .undefined (.enum Known.eEmpty))⟩ := by
  ts_enter_alg lsOrdGopAlg_pin lsOrdGopCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.obj a, .str t], .steps true true true, [], [], none⟩ :: _, .code lsOrdGopCode⟩ _
  gsteps
  refine Steps.trans (ls_ogop H chk s a t sl ps ha hk _) ?_
  gsteps
  exact .refl _

/-- The values of [[Prototype]] an ordinary chain has. -/
def lsProto (v : Val F) : Prop := v = .null ∨ ∃ p : Nat, v = .obj p

/-- OrdinaryGetPrototypeOf(O). -/
theorem ls_ogpo [PinsHold] (s : State F) (a : Nat) (sl : F.Rec (Val F)) (ps : F.Props (Val F)) (v : Val F)
    (ha : s.heap[a]? = some (.object sl ps)) (hp : F.recGet sl 53 = some v) (hv : lsProto v) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨439, 0⟩ [.obj a])⟩ ⟨s, fr, .val v⟩ := by
  ts_enter_alg lsOgpoAlg_pin lsOgpoCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.obj a], .steps false true true, [], [], none⟩ :: _, .code lsOgpoCode⟩ _
  gsteps
  refine Steps.next (step_field _ _ _ _ _ _ _ _ _ _ _ _ _ (ls_readSlot s a sl ps 53 v ha hp)) ?_
  rcases hv with rfl | ⟨p, rfl⟩ <;> (gsteps; exact .refl _)

/-- O.[[GetPrototypeOf]]() of an ordinary object. -/
theorem ls_ordGpo [PinsHold] (s : State F) (a : Nat) (sl : F.Rec (Val F)) (ps : F.Props (Val F)) (v : Val F)
    (ha : s.heap[a]? = some (.object sl ps)) (hp : F.recGet sl 53 = some v) (hv : lsProto v) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨438, 0⟩ [.obj a])⟩
      ⟨s, fr, .val (.comp Known.eNormal v (.enum Known.eEmpty))⟩ := by
  ts_enter_alg lsOrdGpoAlg_pin lsOrdGpoCode_pin
  show Steps _ ⟨s, ⟨_, none, #[.obj a], .steps true true true, [], [], none⟩ :: _, .code lsOrdGpoCode⟩ _
  gsteps
  refine Steps.trans (ls_ogpo H chk s a sl ps v ha hp hv _) ?_
  rcases hv with rfl | ⟨p, rfl⟩ <;> (gsteps; exact .refl _)

/-! ## The ordinary chain: [[HasProperty]], OrdinaryHasProperty, HasProperty -/

/-- No object of the chain has the key `t`. -/
def lsNone (ch : List (F.Props (Val F))) (t : F.Str) : Prop := ∀ ps ∈ ch, F.propsGet ps (.inl t) = none

theorem ls_algIs {o : Option (Val F)} {g : AlgId}
    (h : (match o with
      | some (.alg h) => h == g
      | _ => false) = true) : o = some (.alg g) := by
  split at h
  · rename_i h'
    obtain ⟨c, i⟩ := h'
    obtain ⟨c', i'⟩ := g
    have h2 : (c == c' && i == i') = true := h
    have : c = c' ∧ i = i' := by simpa using h2
    rw [this.1, this.2]
  · cases h

/-- What `ordChain` read of the store at an object of the chain. -/
theorem ls_ordChain_succ {s : State F} {n : Nat} {a : Nat} {ch : List (F.Props (Val F))}
    (h : ordChain s (n + 1) a = some ch) :
    ∃ (sl : F.Rec (Val F)) (ps : F.Props (Val F)), s.heap[a]? = some (.object sl ps) ∧
      F.recGet sl 57 = some (.alg ⟨452, 0⟩) ∧ F.recGet sl 58 = some (.alg ⟨446, 0⟩) ∧
      F.recGet sl 62 = some (.alg ⟨438, 0⟩) ∧
      ((F.recGet sl 53 = some .null ∧ ch = [ps]) ∨
        ∃ (p : Nat) (ch' : List (F.Props (Val F))), F.recGet sl 53 = some (.obj p) ∧ ordChain s n p = some ch' ∧
          ch = ps :: ch') := by
  unfold ordChain at h
  split at h
  · rename_i sl ps ha
    split at h
    · rename_i hm
      refine ⟨sl, ps, ha, ?_⟩
      simp only [ordinaryMethods, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hm
      obtain ⟨h1, h2, h3⟩ := hm
      refine ⟨ls_algIs h1, ls_algIs h2, ls_algIs h3, ?_⟩
      split at h
      · rename_i hp
        exact .inl ⟨hp, (Option.some.inj h).symm⟩
      · rename_i p hp
        obtain ⟨ch', hc, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .inr ⟨p, ch', hp, hc, rfl⟩
      · cases h
    · cases h
  · cases h


set_option maxRecDepth 8000 in
/-- O.[[HasProperty]](P) of an ordinary object whose chain has no property with the key: false, the state as it
was. -/
theorem ls_ordHas [PinsHold] (s : State F) (t : F.Str) : ∀ (n : Nat) (a : Nat) (ch : List (F.Props (Val F))),
    ordChain s n a = some ch → lsNone ch t → ∀ fr : List (Frame F),
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨452, 0⟩ [.obj a, .str t])⟩
      ⟨s, fr, .val (.comp Known.eNormal (.bool false) (.enum Known.eEmpty))⟩ := by
  intro n
  induction n with
  | zero => intro a ch h; cases h
  | succ n ih =>
    intro a ch h hn fr
    obtain ⟨sl, ps, ha, h57, h58, h62, hp⟩ := ls_ordChain_succ h
    have hk : F.propsGet ps (.inl t) = none := by
      rcases hp with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> exact hn ps (by simp)
    ts_enter_alg lsOrdHasAlg_pin lsOrdHasCode_pin
    show Steps _ ⟨s, ⟨_, none, #[.obj a, .str t], .steps true true true, [], [], none⟩ :: _, .code lsOrdHasCode⟩ _
    gsteps
    ts_enter_alg lsOhpAlg_pin lsOhpCode_pin
    show Steps _ ⟨s, ⟨_, none, #[.obj a, .str t, .unbound, .unbound], .steps true true true, [], [], none⟩ :: _,
      .code lsOhpCode⟩ _
    gsteps
    refine Steps.next (ls_step_imethod _ _ _ _ _ _ _ _ _ _ 58 _ _ _ (ls_readSlot s a sl ps 58 _ ha h58)) ?_
    gsteps
    refine Steps.trans (ls_ordGop H chk s a t sl ps ha hk _) ?_
    gsteps
    refine Steps.next (ls_step_imethod _ _ _ _ _ _ _ _ _ _ 62 _ _ _ (ls_readSlot s a sl ps 62 _ ha h62)) ?_
    rcases hp with ⟨h53, rfl⟩ | ⟨p, ch', h53, hch, rfl⟩
    · refine Steps.trans (ls_ordGpo H chk s a sl ps .null ha h53 (.inl rfl) _) ?_
      gsteps
      exact .refl _
    · refine Steps.trans (ls_ordGpo H chk s a sl ps (.obj p) ha h53 (.inr ⟨p, rfl⟩) _) ?_
      gsteps
      cases n with
      | zero => cases hch
      | succ n =>
        obtain ⟨sl', ps', ha', h57', -⟩ := ls_ordChain_succ hch
        refine Steps.next (ls_step_imethod _ _ _ _ _ _ _ _ _ _ 57 _ _ _ (ls_readSlot s p sl' ps' 57 _ ha' h57')) ?_
        gsteps
        refine Steps.trans (ih p ch' hch (fun q hq => hn q (by simp [hq])) _) ?_
        gsteps
        exact .refl _

set_option maxRecDepth 8000 in
/-- HasProperty(O, P) of an ordinary object whose chain has no property with the key: false, the state as it was. -/
theorem ls_hasProperty [PinsHold] (s : State F) (t : F.Str) (n : Nat) (a : Nat) (ch : List (F.Props (Val F)))
    (h : ordChain s n a = some ch) (hn : lsNone ch t) (fr : List (Frame F)) :
    Steps (Ctx.spec Engine.P' H chk) ⟨s, fr, .invoke (.alg ⟨242, 0⟩ [.obj a, .str t])⟩
      ⟨s, fr, .val (.comp Known.eNormal (.bool false) (.enum Known.eEmpty))⟩ := by
  cases n with
  | zero => cases h
  | succ n =>
    obtain ⟨sl, ps, ha, h57, -⟩ := ls_ordChain_succ h
    ts_enter_alg lsHasPropertyAlg_pin lsHasPropertyCode_pin
    show Steps _ ⟨s, ⟨_, none, #[.obj a, .str t], .steps true true true, [], [], none⟩ :: _,
      .code lsHasPropertyCode⟩ _
    gsteps
    refine Steps.next (ls_step_imethod _ _ _ _ _ _ _ _ _ _ 57 _ _ _ (ls_readSlot s a sl ps 57 _ ha h57)) ?_
    gsteps
    refine Steps.trans (ls_ordHas H chk s t (n + 1) a ch h hn _) ?_
    gsteps
    exact .refl _


/-! ## One round -/

/-- The loop's body as `lin` lowers it at step path `p`: the key, the test, the `If` (its steps `tb`), the index's
update `e`. -/
def lsBody (p : List Nat) (k o pk kp : Slot) (tb : Code) (e : Op) : Code :=
  [.site (1 :: p), .let_ pk (.leaf .bang [.call (.alg ⟨208, 0⟩) [.call (.prim 0) [.var k]]]),
    .site (2 :: p), .let_ kp (.leaf .q [.call (.alg ⟨242, 0⟩) [.var o, .var pk]]),
    .site (3 :: p), .br (.bind (.var kp) (.and [.leaf (.isVal false false) [.bound, .const (.val .true)]])) tb [],
    .site (4 :: p), .let_ k e]

set_option maxRecDepth 8000 in
/-- One round of the loop at an index whose key no object of the ordinary chain has: from the round's head to the
next one's, the key and `false` written, the index updated. -/
theorem ls_round [PinsHold] (s : State F) (x : Option Slot) (t : Op)
    (p : List Nat) (k o pk kp : Slot) (tb : Code) (e : Op) (st : IterSt F) (a : AlgId) (nd : Option F.Node)
    (sl : Array (Val F)) (kd : Kind) (p' : List Nat) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F))
    (back : Bool) (r : Nat) (i : Int) (ad : Nat) (key : F.Str) (n : Nat)
    (ch : List (F.Props (Val F))) (k' : Int)
    (hk : sl[k]? = some (.math (.int i))) (ho : sl[o]? = some (.obj ad)) (hpk : pk < sl.size) (hkp : kp < sl.size)
    (hopk : o ≠ pk)
    (ht : TsEv (Ctx.spec Engine.P' H chk) sl t (.bool true))
    (hkeys : LsIntKeys) (hi0 : 0 ≤ i) (hi53 : i < 2 ^ 53)
    (hkey : numberToStr (F.ofNat 10) (lsNum i) = some key)
    (hch : ordChain s n ad = some ch) (hnone : lsNone ch key)
    (he : TsEv (Ctx.spec Engine.P' H chk) ((sl.setIfInBounds pk (.str key)).setIfInBounds kp (.bool false)) e
      (.math (.int k'))) :
    Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, sl, kd, p', K, ci⟩ :: fs,
        .loop (.spend back) ⟨x, .while_ t, p, lsBody p k o pk kp tb e, st, r⟩⟩
      ⟨s, ⟨a, nd, ((sl.setIfInBounds pk (.str key)).setIfInBounds kp (.bool false)).setIfInBounds k
          (.math (.int k')), kd, 4 :: p, K, ci⟩ :: fs,
        .loop (.spend true) ⟨x, .while_ t, p, lsBody p k o pk kp tb e, st, r + 1⟩⟩ := by
  have hk' : sl.getD k .unbound = .math (.int i) := by simp [Array.getD_eq_getD_getElem?, hk]
  mstep
  have hround : Steps (Ctx.spec Engine.P' H chk)
      ⟨s, ⟨a, nd, sl, kd, p', K, ci⟩ :: fs,
        .loop .round ⟨x, .while_ t, p, lsBody p k o pk kp tb e, st, r + 1⟩⟩
      ⟨s, ⟨a, nd, ((sl.setIfInBounds pk (.str key)).setIfInBounds kp (.bool false)).setIfInBounds k
          (.math (.int k')), kd, 4 :: p, K, ci⟩ :: fs,
        .loop (.spend true) ⟨x, .while_ t, p, lsBody p k o pk kp tb e, st, r + 1⟩⟩ := by
    mstep
    refine Steps.trans (ht _ _ _ _ _ _ _ _) ?_
    iterate 5 mstep
    ts_ev TsEv.prim1 (TsEv.var hk' (by simp)) rfl rfl (ls_primF i)
    mstep
    refine Steps.trans (ls_toString H chk hkeys i hi0 hi53 key hkey _ _) ?_
    have ho1 : (sl.setIfInBounds pk (.str key)).getD o .unbound = .obj ad := by
      simp [Array.getD_eq_getD_getElem?, Ne.symm hopk, ho]
    have hpk1 : (sl.setIfInBounds pk (.str key)).getD pk .unbound = .str key := by
      simp [Array.getD_eq_getD_getElem?, hpk]
    have hkp2 : ((sl.setIfInBounds pk (.str key)).setIfInBounds kp (.bool false)).getD kp .unbound = .bool false := by
      simp [Array.getD_eq_getD_getElem?, hkp]
    iterate 7 mstep
    refine Steps.next (step_var _ _ _ _ o (.obj ad) ho1 (by simp)) ?_
    mstep
    refine Steps.next (step_var _ _ _ _ pk (.str key) hpk1 (by simp)) ?_
    mstep
    refine Steps.trans (ls_hasProperty H chk s key n ad ch hch hnone _) ?_
    gsteps
    refine Steps.next (step_var _ _ _ _ kp (.bool false) hkp2 (by simp)) ?_
    gsteps
    ts_ev he
    mstep
    mstep
    exact .refl _
  cases back
  · exact hround
  · mstep
    exact hround


/-! ## The rounds -/

/-- The loop's condition: `k < len`, or `k ≥ 0` (no bound: descending). -/
def lsTest (k : Slot) : Option Slot → Op
  | some len => .leaf (.rel .lt) [.var k, .var len]
  | none => .leaf (.rel .ge) [.var k, .const (.math .none (.num (.dec 0)))]

/-- The index's update: `k + 1`, or `k - 1` descending. -/
def lsUpd (k : Slot) : Option Slot → Op
  | some _ => .leaf (.bin .add) [.var k, .const (.math .none (.num (.dec 1)))]
  | none => .leaf (.bin .sub) [.var k, .const (.math .none (.num (.dec 1)))]

/-- The index `j` rounds after `i`. -/
def lsStep : Option Slot → Int → Nat → Int
  | some _, i, j => i + j
  | none, i, j => i - j

/-- The key of the index `v`, as the skip writes it. -/
def lsKeyStr (v : Int) : F.Str := F.strLit (toString v.toNat)

theorem ls_key (hkeys : LsIntKeys) (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 53) :
    numberToStr (F.ofNat 10) (lsNum v) = some (lsKeyStr v) := by
  by_cases hv : v = 0
  · subst hv
    have e : lsNum 0 = F.numZero false := rfl
    have e2 : lsKeyStr 0 = F.strLit "0" := by
      show F.strLit (toString (0 : Nat)) = _
      have e0 : toString (0 : Nat) = "0" := by
        rw [Nat.toString_eq_repr, ← String.toList_inj, Nat.toList_repr, Nat.toDigits_zero]
        rfl
      rw [e0]
    rw [e, e2]
    simp only [numberToStr, fromStep1]
    rfl
  · have e : lsNum v = F.numOf (Model.MathVal.int v) := by simp [lsNum, Model.MathVal.eq, hv]
    have := hkeys.digits v.toNat (by omega) (by omega)
    rw [Int.toNat_of_nonneg h0] at this
    rw [e, this]
    simp [lsKeyStr]

/-- The slots after a round: the key, `false`, the index. -/
def lsPost (k pk kp : Slot) (sl : Array (Val F)) (key : F.Str) (k' : Int) : Array (Val F) :=
  ((sl.setIfInBounds pk (.str key)).setIfInBounds kp (.bool false)).setIfInBounds k (.math (.int k'))

/-- What the skip checks of the loop's slots, apart from the index. -/
structure LsSlots (k o pk kp : Slot) (bound : Option Slot) (sl : Array (Val F)) (ad : Nat) : Prop where
  ho : sl[o]? = some (.obj ad)
  hpk : pk < sl.size
  hkp : kp < sl.size
  kpk : k ≠ pk
  kkp : k ≠ kp
  ok : o ≠ k
  opk : o ≠ pk
  okp : o ≠ kp
  pkkp : pk ≠ kp
  hb : ∀ len, bound = some len → len ≠ k ∧ len ≠ pk ∧ len ≠ kp

/-- The loop's condition holds for `g + 1` rounds from `i`, at indices below 2^53. -/
def lsCond (bound : Option Slot) (sl : Array (Val F)) (i : Int) (g : Nat) : Prop :=
  match bound with
  | some len => ∃ n : Int, sl[len]? = some (.math (.int n)) ∧ i + g < n ∧ i + g < 2 ^ 53
  | none => (g : Int) ≤ i ∧ i < 2 ^ 53

theorem ls_post_k {k pk kp : Slot} {sl : Array (Val F)} {v : Val F} (key : F.Str) (k' : Int)
    (hk : sl[k]? = some v) : (lsPost k pk kp sl key k')[k]? = some (.math (.int k')) := by
  have hlt : k < sl.size := (Array.getElem?_eq_some_iff.mp hk).1
  simp [lsPost, hlt]

theorem ls_post_other {k pk kp : Slot} {sl : Array (Val F)} (key : F.Str) (k' : Int) {y : Slot}
    (h1 : y ≠ k) (h2 : y ≠ pk) (h3 : y ≠ kp) : (lsPost k pk kp sl key k')[y]? = sl[y]? := by
  simp [lsPost, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem ls_post_slots {k o pk kp : Slot} {bound : Option Slot} {sl : Array (Val F)} {ad : Nat}
    (h : LsSlots k o pk kp bound sl ad) (key : F.Str) (k' : Int) :
    LsSlots k o pk kp bound (lsPost k pk kp sl key k') ad where
  ho := (ls_post_other key k' h.ok h.opk h.okp).trans h.ho
  hpk := by simp [lsPost, h.hpk]
  hkp := by simp [lsPost, h.hkp]
  kpk := h.kpk
  kkp := h.kkp
  ok := h.ok
  opk := h.opk
  okp := h.okp
  pkkp := h.pkkp
  hb := h.hb

theorem ls_post_cond {k o pk kp : Slot} {bound : Option Slot} {sl : Array (Val F)} {ad : Nat}
    (h : LsSlots k o pk kp bound sl ad) (key : F.Str) (k' : Int) {i : Int} {g : Nat}
    (hc : lsCond bound sl i (g + 1)) : lsCond bound (lsPost k pk kp sl key k') (lsStep bound i 1) g := by
  cases bound with
  | none =>
    simp only [lsCond, lsStep] at hc ⊢
    omega
  | some len =>
    obtain ⟨n, hn, h1, h2⟩ := hc
    obtain ⟨a1, a2, a3⟩ := h.hb len rfl
    refine ⟨n, (ls_post_other key k' a1 a2 a3).trans hn, ?_, ?_⟩ <;> simp only [lsStep] <;> omega

theorem ls_post_post {k pk kp : Slot} {sl : Array (Val F)} (key key' : F.Str) (k' k'' : Int) :
    lsPost k pk kp (lsPost k pk kp sl key k') key' k'' = lsPost k pk kp sl key' k'' := by
  apply Array.ext_getElem?
  intro y
  simp only [lsPost, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  grind

theorem ls_test (X : Ctx F) {k : Slot} {bound : Option Slot} {sl : Array (Val F)} {i : Int} {g : Nat}
    (hk : sl[k]? = some (.math (.int i))) (h0 : 0 ≤ i) (hc : lsCond bound sl i g) :
    TsEv X sl (lsTest k bound) (.bool true) := by
  have hk' : sl.getD k .unbound = .math (.int i) := by simp [Array.getD_eq_getD_getElem?, hk]
  cases bound with
  | none =>
    refine TsEv.ge (TsEv.var hk' (by simp)) ts_zero ?_
    simp [ge?, lt?, eq?, Model.MathVal.lt, Model.MathVal.eq, bind, Option.bind]
    omega
  | some len =>
    obtain ⟨n, hn, h1, h2⟩ := hc
    have hn' : sl.getD len .unbound = .math (.int n) := by simp [Array.getD_eq_getD_getElem?, hn]
    refine TsEv.lt (TsEv.var hk' (by simp)) (TsEv.var hn' (by simp)) ?_
    simp [lt?, Model.MathVal.lt]
    omega

theorem ls_upd (X : Ctx F) {k : Slot} (bound : Option Slot) {sl : Array (Val F)} {i : Int}
    (hk : sl[k]? = some (.math (.int i))) :
    TsEv X sl (lsUpd k bound) (.math (.int (lsStep bound i 1))) := by
  have hk' : sl.getD k .unbound = .math (.int i) := by simp [Array.getD_eq_getD_getElem?, hk]
  cases bound with
  | none =>
    refine TsEv.bin (TsEv.var hk' (by simp)) ts_one ?_
    rw [ts_op_sub]
    simp [lsStep, Engine.Accel.one, Model.MathVal.add, Model.MathVal.neg]
    omega
  | some len =>
    refine TsEv.bin (TsEv.var hk' (by simp)) ts_one ?_
    rw [ts_op_add]
    simp [lsStep, Engine.Accel.one, Model.MathVal.add]

theorem ls_step_zero (bound : Option Slot) (i : Int) : lsStep bound i 0 = i := by
  cases bound <;> simp [lsStep]

theorem ls_step_succ (bound : Option Slot) (i : Int) (j : Nat) :
    lsStep bound (lsStep bound i 1) j = lsStep bound i (j + 1) := by
  cases bound <;> simp [lsStep] <;> omega

theorem ls_step_range {bound : Option Slot} {sl : Array (Val F)} {i : Int} {g : Nat} (h0 : 0 ≤ i)
    (hc : lsCond bound sl i g) (j : Nat) (hj : j ≤ g) : 0 ≤ lsStep bound i j ∧ lsStep bound i j < 2 ^ 53 := by
  cases bound with
  | none =>
    simp only [lsCond, lsStep] at hc ⊢
    omega
  | some len =>
    obtain ⟨n, -, h1, h2⟩ := hc
    simp only [lsStep]
    omega

/-- The loop, at its round `r`. -/
def lsLoop (x : Option Slot) (p : List Nat) (k o pk kp : Slot) (bound : Option Slot)
    (tb : Code) (st : IterSt F) (r : Nat) : Loop F :=
  ⟨x, .while_ (lsTest k bound), p, lsBody p k o pk kp tb (lsUpd k bound), st, r⟩

set_option maxRecDepth 8000 in
/-- `g + 1` rounds of the loop from the index `i`, at indices whose keys no object of the ordinary chain has. -/
theorem ls_rounds [PinsHold] (hkeys : LsIntKeys) (x : Option Slot)
    (p : List Nat) (k o pk kp : Slot) (bound : Option Slot) (tb : Code) (st : IterSt F) (a : AlgId)
    (nd : Option F.Node) (kd : Kind) (K : List (Kont F)) (ci : Option Nat) (fs : List (Frame F)) (ad n : Nat)
    (ch : List (F.Props (Val F))) :
    ∀ (g : Nat) (i : Int) (s : State F) (sl : Array (Val F)) (p' : List Nat) (back : Bool) (r : Nat),
      sl[k]? = some (.math (.int i)) → LsSlots k o pk kp bound sl ad → 0 ≤ i → lsCond bound sl i g →
      ordChain s n ad = some ch → (∀ j ≤ g, lsNone ch (lsKeyStr (lsStep bound i j))) →
      Steps (Ctx.spec Engine.P' H chk)
        ⟨s, ⟨a, nd, sl, kd, p', K, ci⟩ :: fs, .loop (.spend back) (lsLoop x p k o pk kp bound tb st r)⟩
        ⟨s,
          ⟨a, nd, lsPost k pk kp sl (lsKeyStr (lsStep bound i g)) (lsStep bound i (g + 1)), kd, 4 :: p, K, ci⟩ :: fs,
          .loop (.spend true) (lsLoop x p k o pk kp bound tb st (r + g + 1))⟩ := by
  intro g
  induction g with
  | zero =>
    intro i s sl p' back r hk hs h0 hc hch hno
    have hr := ls_step_range h0 hc 0 (Nat.le_refl 0)
    rw [ls_step_zero] at hr
    have hsl2 : ((sl.setIfInBounds pk (.str (lsKeyStr i))).setIfInBounds kp (.bool false))[k]? =
        some (.math (.int i)) := by
      simp [Ne.symm hs.kpk, Ne.symm hs.kkp, hk]
    have h1 := ls_round H chk s x (lsTest k bound) p k o pk kp tb (lsUpd k bound) st a nd sl kd p' K ci
      fs back r i ad (lsKeyStr i) n ch (lsStep bound i 1) hk hs.ho hs.hpk hs.hkp hs.opk
      (ls_test _ hk h0 hc) hkeys hr.1 hr.2 (ls_key hkeys i hr.1 hr.2) hch
      (by simpa [ls_step_zero] using hno 0 (Nat.le_refl 0))
      (ls_upd _ bound hsl2)
    simpa [ls_step_zero, lsLoop, lsPost] using h1
  | succ g ih =>
    intro i s sl p' back r hk hs h0 hc hch hno
    have hr := ls_step_range h0 hc 0 (Nat.zero_le _)
    rw [ls_step_zero] at hr
    have hr1 := ls_step_range h0 hc 1 (by omega)
    have hsl2 : ((sl.setIfInBounds pk (.str (lsKeyStr i))).setIfInBounds kp (.bool false))[k]? =
        some (.math (.int i)) := by
      simp [Ne.symm hs.kpk, Ne.symm hs.kkp, hk]
    have hc0 : lsCond bound sl i 0 := by
      cases bound with
      | none => simp only [lsCond] at hc ⊢; omega
      | some len =>
        obtain ⟨n', hn, h1, h2⟩ := hc
        exact ⟨n', hn, by omega, by omega⟩
    have h1 := ls_round H chk s x (lsTest k bound) p k o pk kp tb (lsUpd k bound) st a nd sl kd p' K ci
      fs back r i ad (lsKeyStr i) n ch (lsStep bound i 1) hk hs.ho hs.hpk hs.hkp hs.opk
      (ls_test _ hk h0 hc0) hkeys hr.1 hr.2 (ls_key hkeys i hr.1 hr.2) hch
      (by simpa [ls_step_zero] using hno 0 (Nat.zero_le _))
      (ls_upd _ bound hsl2)
    have h2 := ih (lsStep bound i 1) s (lsPost k pk kp sl (lsKeyStr i) (lsStep bound i 1)) (4 :: p)
      true (r + 1) (ls_post_k _ _ hk) (ls_post_slots hs _ _) hr1.1 (ls_post_cond hs _ _ hc) hch
      (fun j hj => by rw [ls_step_succ]; exact hno (j + 1) (by omega))
    rw [ls_step_succ, ls_step_succ, ls_post_post] at h2
    rw [show r + 1 + g + 1 = r + (g + 1) + 1 by omega] at h2
    exact Steps.trans h1 h2


end Engine.Machine
