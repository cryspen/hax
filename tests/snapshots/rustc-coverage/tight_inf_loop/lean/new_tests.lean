
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


namespace new_tests.rustc_coverage__tight_inf_loop

--  @fail(extraction): lean(HAX0001), proverif(HAX0008), coq(HAX0001), fstar(HAX0001)
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  if false then
    (rust_primitives.hax.never_to_any
      (rust_primitives.hax.Tuple2.mk sorry rust_primitives.hax.Tuple0.mk))
  else
    (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__tight_inf_loop

