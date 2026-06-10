import LeanBarrett.Extraction.Funs
import Hax

open Std.Do Aeneas lean_barrett CoreModels
set_option mvcgen.warning false

attribute [local spec] barrett_reduce barrett_reduce_precondition barret_reduce_postcondition
  core.I64.Insts.CoreConvertFromI32.from

attribute [local grind =]
  Int32.toInt_toInt64 Int64.ofBitVec_int32ToBitVec
  Int64.toInt_inj Int32.toInt_inj
  Int64.le_iff_toInt_le Int32.lt_iff_toInt_lt

local grind_pattern Int32.toInt64_ofNat => (@OfNat.ofNat Int32 n _).toInt64

theorem Int.div_le_div_of_mul_le_mul {a b c d : Int} (h : a * d ≤ c * b) (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d := by
  rw [Int.le_ediv_iff_mul_le hd]
  apply Int.le_of_mul_le_mul_right _ hb
  rw [Int.mul_assoc, Int.mul_comm d b, ← Int.mul_assoc]
  calc a / b * b * d
      ≤ a * d := Int.mul_le_mul_of_nonneg_right (Int.ediv_mul_le a (by omega)) (by omega)
    _ ≤ c * b := h

open Std

@[grind =]
theorem val_cast (a : I32) : (IScalar.cast .I64 a).val = a.val := by
  apply BitVec.toInt_signExtend_of_le; grind

@[grind =]
theorem cast_lemma (a : I64) (hmin : - 2 ^ 31 ≤ a.val) (hmax : a.val < 2 ^ 31) :
    (IScalar.cast IScalarTy.I32 a).val = a.val := by
  apply Eq.trans (BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ _)
    <;> grind

@[spec]
theorem neg_spec32 (a : I32)
    (h1 : a.val = - 2 ^ 31 → (Q.2.1 .integerOverflow).down)
    (h2 : ∀ r, r.val = - a.val → (Q.1 r).down) :
    ⦃ ⌜ True ⌝ ⦄ (-. a) ⦃ Q ⦄ := by
  show ⦃ _ ⦄ IScalar.neg a ⦃ _ ⦄
  unfold IScalar.neg IScalar.tryMk
  have heq := IScalar.tryMkOpt_eq .I32 (-a.val)
  cases hopt : IScalar.tryMkOpt .I32 (-a.val) with
  | none =>
    rw [hopt] at heq
    simp only [Result.ofOption]
    apply Result.fail_spec
    apply h1
    have ha := a.hBounds
    simp only [IScalar.inBounds, IScalarTy.I32_numBits_eq] at heq ha
    grind
  | some r =>
    rw [hopt] at heq
    simp only [Result.ofOption]
    apply Result.ok_spec
    apply h2; exact heq.1

@[spec]
theorem neg_spec64 (a : I64)
  (h1 : a.val = - 2 ^ 63 → (Q.2.1 .integerOverflow).down)
  (h2 : ∀ r, r.val = - a.val → (Q.1 r).down) :
  ⦃ ⌜ True ⌝ ⦄ (-. a) ⦃ Q ⦄ := by
  show ⦃ _ ⦄ IScalar.neg a ⦃ _ ⦄
  unfold IScalar.neg IScalar.tryMk
  have heq := IScalar.tryMkOpt_eq .I64 (-a.val)
  cases hopt : IScalar.tryMkOpt .I64 (-a.val) with
  | none =>
    rw [hopt] at heq
    simp only [Result.ofOption]
    apply Result.fail_spec
    apply h1
    have ha := a.hBounds
    simp only [IScalar.inBounds, IScalarTy.I64_numBits_eq] at heq ha
    grind
  | some r =>
    rw [hopt] at heq
    simp only [Result.ofOption]
    apply Result.ok_spec
    apply h2; exact heq.1

@[spec]
theorem rShift_spec32 (a : I64) (b : I32) (hmin : b.val ≥ 0) (hmax : b.val < 32) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
  hax_mvcgen
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

@[spec]
theorem rShift_spec64 (a b : I64) (hmin : b.val ≥ 0) (hmax : b.val < 64) :
    ⦃ ⌜ True ⌝ ⦄ (a >>> b) ⦃ ⇓ r => ⌜ r.val = a.val / (2 ^ b.val.toNat) ⌝ ⦄ := by
  simp only [HShiftRight.hShiftRight, IScalar.shiftRight_IScalar, IScalar.shiftRight]
  hax_mvcgen
    <;> grind [IScalar.val, Int.shiftRight_eq_div_pow]

theorem barrett_reduce_spec value
  (h : (barrett_reduce_precondition value).holds):
    ⦃ ⌜ True ⌝ ⦄
    barrett_reduce value
    ⦃ ⇓ r => ⌜ (barret_reduce_postcondition value r).holds ⌝ ⦄ := by
  hax_mvcgen
    <;> try simp [BARRETT_MULTIPLIER, BARRETT_R, BARRETT_SHIFT, FIELD_MODULUS] at *
    <;> try grind
