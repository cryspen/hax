import Adc.Extraction.Funs
import Adc.Extraction.Specs
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace adc

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
    <;> try simp_all only [opaque32_def, UScalar.cast_val_eq, UScalarTy.numBits, Nat.shiftLeft_eq,
          Nat.shiftRight_eq_div_pow, U64.size, UScalar.le_equiv]; scalar_tac

end adc
