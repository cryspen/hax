import LeanAdc.Extraction.Funs
import LeanAdc.Extraction.Specs
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace lean_adc

set_option maxHeartbeats 1000000

-- This spec annotation is missing in Aeneas:
attribute [local spec] uncurry

-- This is a workaround for a bug in `mvcgen` where `mvcgen` fails to terminate
-- when encountering a term like `>>> 32#u64`:
@[irreducible] def opaque32 := 32#u64
lemma opaque32_def : opaque32 = 32#u64 := by unfold opaque32; rfl

/-- Correctness of 32-bit addition with carry. -/
theorem adc_u32.spec.proof (a b carry_in : U32) : adc_u32.spec a b carry_in := by
  unfold adc_u32.spec adc_u32.pre adc_u32.post adc_u32
  rw [← opaque32_def] -- workaround for `mvcgen` bug
  hax_mvcgen
  case vc4.hmax =>
    simp_all [opaque32_def, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, U64.size]
    grind only [Nat.pow_pos, = UScalar.ofNatCore_val_eq, = UScalarTy.U64_numBits_eq,
      U64.max_def, U64.numBits_def]
  case vc5 =>
    simp_all only [opaque32_def, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, U64.size]
    scalar_tac
  case vc6.hQ =>
    simp_all only [opaque32_def, UScalar.cast_val_eq, UScalarTy.numBits,
      Nat.shiftRight_eq_div_pow, UScalar.le_equiv]
    scalar_tac
  all_goals grind [UScalar.cast_val_eq, opaque32_def]

end lean_adc
