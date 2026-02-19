
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__assert_not

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (hax_lib.assert true);
  let _ ← (hax_lib.assert (← (core_models.ops.bit.Not.not false)));
  let _ ←
    (hax_lib.assert
      (← (core_models.ops.bit.Not.not (← (core_models.ops.bit.Not.not true)))));
  let _ ←
    (hax_lib.assert
      (← (core_models.ops.bit.Not.not
        (← (core_models.ops.bit.Not.not
          (← (core_models.ops.bit.Not.not false)))))));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__assert_not

