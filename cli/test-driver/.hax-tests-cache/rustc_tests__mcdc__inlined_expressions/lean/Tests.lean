
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

def Tests.Rustc_tests__mcdc__inlined_expressions.inlined_instance
  (a : Bool)
  (b : Bool)
  : Result Bool
  := do
  (← a &&? b)

def Tests.Rustc_tests__mcdc__inlined_expressions.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__inlined_expressions.inlined_instance
        true
        false));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__inlined_expressions.inlined_instance
        false
        true));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__inlined_expressions.inlined_instance
        true
        true));
  Rust_primitives.Hax.Tuple0.mk