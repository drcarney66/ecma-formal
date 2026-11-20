module

public import Engine.Proofs.Maps
public import Engine.Proofs.Num
public import Engine.Proofs.CharSet
public import Engine.Proofs.Bytes
public import Engine.Proofs.Radix

@[expose] public section

/-!
# The engine's model meets the laws of the specification's sorts

`Model.Laws Impl`, from the laws of mathematical values and BigInts (`Math`), Numbers (`Num`), Strings, Symbols
and addresses (`Str`), Lists (`Seq`), Records, property tables and the store (`Maps`); a Parse Node is its tree, compared field by field (`Node.same_iff`).
-/

namespace Engine.Impl
open Ecma

/-- The engine's model meets the laws. -/
theorem laws : Model.Laws Impl where
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  add_neg := add_neg
  sub_def := sub_def
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  mul_add := mul_add
  div_mul := div_mul
  zero_ne_one := zero_ne_one
  lt_irrefl := lt_irrefl
  lt_trans := lt_trans
  lt_total := lt_total
  add_lt_add := add_lt_add
  mul_pos := mul_pos
  eq_iff := eq_iff
  ofNat_add := ofNat_add
  pow_zero := pow_zero
  pow_succ := pow_succ
  floor_isInt := floor_isInt
  floor_le := floor_le
  lt_floor_add_one := lt_floor_add_one
  decExp_spec x hx := by
    have h0 : 0 < x.toQ := (Engine.Model.MathVal.lt_iff _ _).1 hx
    obtain ⟨a, b⟩ := Engine.Model.Digits.decExp_spec h0
    refine ⟨rfl, ?_, ?_⟩
    · show Engine.Model.MathVal.lt x (Engine.Model.MathVal.pow (.int ((10 : Nat) : Int)) (.int (Engine.Model.Digits.decExp x.toQ))) = false
      rw [Engine.Model.MathVal.lt_eq, toQ_pow_int (by decide)]
      exact decide_eq_false (Rat.not_lt.2 a)
    · show Engine.Model.MathVal.lt x (Engine.Model.MathVal.pow (.int ((10 : Nat) : Int)) (.int (Engine.Model.Digits.decExp x.toQ + 1))) = true
      rw [Engine.Model.MathVal.lt_eq, toQ_pow_int (by decide)]
      exact decide_eq_true b
  isInt_iff := isInt_iff
  numView_nan := numView_nan
  numView_inf := numView_inf
  numView_zero := numView_zero
  num := numLaws
  bigVal_bigOf := bigVal_bigOf
  bigVal_isInt := bigVal_isInt
  bigVal_inj := bigVal_inj
  strAt_some := strAt_some
  str_ext := str_ext
  strConcat_len := strConcat_len
  strConcat_at := strConcat_at
  strSub_len := strSub_len
  strSub_at := strSub_at
  strOfUnit_len := strOfUnit_len
  strOfUnit_at := strOfUnit_at
  strRepeat_zero := Engine.Model.strRepeat_zero
  strRepeat_succ := Engine.Model.strRepeat_succ
  intToRadix_digit := Engine.Model.intToRadix_digit
  intToRadix_div := Engine.Model.intToRadix_div
  strEq_iff := strEq_iff
  strLit_units := strLit_units
  strUnits_len := strUnits_len
  strUnits_at := strUnits_at
  symEq_iff := symEq_iff
  symDesc_new := symDesc_new
  symNew_inj := symNew_inj
  addrEq_iff := addrEq_iff
  nodeEq_iff := Engine.Model.Node.same_iff
  seqLen_nat := seqLen_nat
  seqGet_some := seqGet_some
  seqGet_lt := seqGet_lt
  seq_ext := seq_ext
  seqLen_nil := seqLen_nil
  seqGet_nil := seqGet_nil
  seqLen_push := seqLen_push
  seqGet_push := seqGet_push
  seqLen_cons := seqLen_cons
  seqGet_cons := seqGet_cons
  seqLen_set := seqLen_set
  seqGet_set := seqGet_set
  seqLen_concat := seqLen_concat
  seqGet_concat := seqGet_concat
  seqLen_remove := seqLen_remove
  seqGet_remove := seqGet_remove
  seqRemove_none := seqRemove_none
  seqLen_repeat := seqLen_repeat
  seqGet_repeat := seqGet_repeat
  seqFoldl_nil := seqFoldl_nil
  seqFoldl_push := seqFoldl_push
  recGet_empty := recGet_empty
  recGet_set := recGet_set
  recGet_del := recGet_del
  recKeys_mem := recKeys_mem
  recKeys_once := recKeys_once
  propsGet_empty := propsGet_empty
  propsGet_put_self := propsGet_put_self
  propsGet_put_other := propsGet_put_other
  propsGet_del_self := propsGet_del_self
  propsGet_del_other := propsGet_del_other
  propsKeys_mem := propsKeys_mem
  propsKeys_once := propsKeys_once
  propsKeys_put_new := propsKeys_put_new
  propsKeys_put_old := propsKeys_put_old
  propsKeys_del := propsKeys_del
  propsDel_absent := propsDel_absent
  heapGet_empty := heapGet_empty
  heapAlloc_fresh := heapAlloc_fresh
  heapAlloc_get_self := heapAlloc_get_self
  heapAlloc_get_other := heapAlloc_get_other
  heapGet_set_self := heapGet_set_self
  heapGet_set_other := heapGet_set_other
  heapSet_none := heapSet_none
  csSize_nat := csSize_nat_law
  csGet_some := csGet_some_law
  csGet_lt := csGet_lt_law
  csGet_distinct := csGet_distinct_law
  csHas_exists := csHas_exists_law
  csHas_empty := csEmpty_law
  csHas_add := csAdd_law
  csHas_interval := csInterval_law
  csHas_union := csUnion_law
  csHas_inter := csInter_law
  csHas_diff := csDiff_law
  csAllSingle_iff := csAllSingle_iff_law
  csHas_singles := csHas_singles_law
  csFromProp_some := csFromProp_some_law
  csHas_fromProp := csHas_fromProp_law
  csHas_noScf := csHas_noScf_law
  csHas_canonExtra := csHas_canonExtra_law
  csHasCanon_iff := csHasCanon_iff_law
  bytes := byteLaws

end Engine.Impl
