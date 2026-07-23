import Hax

/-! # Tests for `Hax.forLoopWithInvariant`

Not part of the regular proof-library build: `Tests` is not a default target, so it is
only built when requested explicitly (`lake build Tests`). These exercise the user-facing
spec lemmas end-to-end on concrete loops. -/

set_option mvcgen.warning false

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
open Std.Tactic

namespace Hax.Tests

/-! ## End-to-end signed test

A concrete `for i in (0 : i32) .. 5` loop with the invariant `acc.val = 0`, proven purely
through the signed `forLoopWithInvariant_spec` (which itself routes through `loop_range_spec`
and the signed `IteratorRange_next_spec`). No extraction is involved: `lake build Tests`
alone validates the signed end-to-end path. -/

example :
    ⦃ ⌜ True ⌝ ⦄
    Hax.forLoopWithInvariant core.I32.Insts.CoreIterRangeStep
      (fun (_ : I32) (acc : I32) => (ok (acc.val = 0) : Result Prop))
      (fun (_ : I32) (acc : I32) => (ok acc : Result I32))
      { start := (0#i32), «end» := (5#i32) } (0#i32)
    ⦃ ⇓ r => ⌜ (ok (r.val = 0) : Result Prop).holds ⌝ ⦄ := by
  refine forLoopWithInvariant_spec
    (fun _ acc => ok acc) (0#i32) (0#i32) (5#i32)
    (fun _ acc => ok (acc.val = 0)) (by scalar_tac) ?_ ?_
  · -- h_init : `(inv 0 0).holds`, i.e. `(0 : I32).val = 0`
    simp [Result.holds, Triple, WP.wp, PredTrans.apply]
  · -- h_step : the identity body preserves `acc.val = 0`
    intro acc i _ _ hinv
    have hacc : acc.val = 0 := by
      simpa [Result.holds, Triple, WP.wp, PredTrans.apply] using hinv
    simp [Triple, WP.wp, PredTrans.apply, Result.holds, hacc]

end Hax.Tests
