
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


namespace new_tests.legacy__backend_specific_quotes__lib

@[spec]
def decorated_with_an_fstar_quote (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def decorated_with_a_coq_quote (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

-- a verbatim Lean comment

@[spec]
def decorated_with_a_lean_quote (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

-- another verbatim Lean comment

--  Same, but with a `requires` clause: the F* backend looks up the `Requires`
--  role on this item, and used to choke on the unrelated dangling `ItemQuote`
--  marker while doing so.
def quoted_and_decorated (x : u8) : RustM u8 := do (x +? (1 : u8))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def quoted_and_decorated.spec (x : u8) :
    Spec
      (requires := do (x <? (100 : u8)))
      (ensures := fun _ => pure True)
      (quoted_and_decorated (x : u8)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [quoted_and_decorated] <;> bv_decide
}

end new_tests.legacy__backend_specific_quotes__lib

