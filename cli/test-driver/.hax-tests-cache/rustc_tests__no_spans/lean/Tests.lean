
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

def Tests.Rustc_tests__no_spans.affected_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
  := do
  (fun _ => (do
      Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0))

def Tests.Rustc_tests__no_spans.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Core.Ops.Function.Fn.call
        (← Tests.Rustc_tests__no_spans.affected_function
            Rust_primitives.Hax.Tuple0.mk)
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk