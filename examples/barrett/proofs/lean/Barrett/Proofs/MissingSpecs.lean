-- Missing core model specs, to upstream
import Aeneas
import Barrett.Extraction.Types
import Barrett.Extraction.Funs
import Barrett.Extraction.Specs
open Aeneas Aeneas.Std Result ControlFlow Error
open Std.Do Aeneas barrett CoreModels
set_option mvcgen.warning false

@[grind =]
theorem cast_lemma (a : I64) (hmin : - 2 ^ 31 ≤ a.val) (hmax : a.val < 2 ^ 31) :
    (IScalar.cast IScalarTy.I32 a).val = a.val := by
  apply Eq.trans (BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ _)
    <;> grind

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

@[spec]
theorem I32_rem_euclid_spec (x y : Std.I32) (hy : y.val ≠ 0) :
    ⦃ ⌜ True ⌝ ⦄
    core.num.I32.rem_euclid x y
    ⦃ ⇓ r => ⌜ r.val = x.val % y.val ⌝ ⦄ := by
  mvcgen [core.num.I32.rem_euclid, rust_primitives.arithmetic.rem_euclid_i32, irem_euclid]
  grind [Int.emod_nonneg x.val hy, Int.emod_lt_abs x.val hy, IScalar.val]
