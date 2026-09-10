
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__assert_not

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (hax_lib.assert true);
  let _ ← (hax_lib.assert (← (!? false)));
  let _ ← (hax_lib.assert (← (!? (← (!? true)))));
  let _ ← (hax_lib.assert (← (!? (← (!? (← (!? false)))))));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__assert_not

