import Adc.Extraction
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow Error
open Std.Do

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace adc

set_option maxHeartbeats 1000000

/-- Correctness of 32-bit addition with carry. -/
theorem adc_u32.spec.proof (a b carry_in : U32) : adc_u32.spec a b carry_in := by
  unfold adc_u32.spec adc_u32.pre adc_u32.post adc_u32
  hax_mvcgen
  all_goals
    simp_all only [UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftRight_eq_div_pow,
      UScalar.le_equiv, Nat.reducePow, Int.natCast_emod, Nat.cast_add, Nat.cast_ofNat,
      UScalar.ofNatCore_val_eq, Int.natCast_ediv, Int.reduceToNat, Int.reducePow, beq_iff_eq]
    scalar_tac


end adc
