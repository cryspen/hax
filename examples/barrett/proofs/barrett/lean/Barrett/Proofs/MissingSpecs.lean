-- Missing core model specs, to upstream
import Aeneas
import Barrett.Extraction.Types
import Barrett.Extraction.Funs
import Barrett.Extraction.Specs
open Aeneas Aeneas.Std Result ControlFlow Error
open Std.Do Aeneas barrett CoreModels
set_option mvcgen.warning false

@[spec]
theorem I32_rem_euclid_spec (x y : Std.I32) (hy : y.val ≠ 0) :
    ⦃ ⌜ True ⌝ ⦄
    core.num.I32.rem_euclid x y
    ⦃ ⇓ r => ⌜ r.val = x.val % y.val ⌝ ⦄ := by
  mvcgen [core.num.I32.rem_euclid, rust_primitives.arithmetic.rem_euclid_i32, irem_euclid]
  grind [Int.emod_nonneg x.val hy, Int.emod_lt_abs x.val hy, IScalar.val]
