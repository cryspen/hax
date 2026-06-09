
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


namespace new_tests.legacy__tuples__lib

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def project_tuple1 (_ : rust_primitives.hax.Tuple0) : RustM u8 := do
  let tuple1 : (rust_primitives.hax.Tuple1 u8) :=
    (rust_primitives.hax.Tuple1.mk (3 : u8));
  (pure (rust_primitives.hax.Tuple1._0 tuple1))

end new_tests.legacy__tuples__lib

