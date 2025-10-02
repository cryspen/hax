
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

def Tests.Rustc_tests__assert_not.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Hax_lib.assert true));
  let _ ← (pure (← Hax_lib.assert (← Core.Ops.Bit.Not.not false)));
  let _ ← (pure
    (← Hax_lib.assert (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not true))));
  let _ ← (pure
    (← Hax_lib.assert
        (← Core.Ops.Bit.Not.not
            (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not false)))));
  Rust_primitives.Hax.Tuple0.mk