
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

def Tests.Rustc_tests__closure_unit_return.explicit_unit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let
    closure : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0 ←
    (pure
    (fun _ => (do
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _ ← (pure
    (← Core.Mem.drop
        Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
        closure));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__closure_unit_return.implicit_unit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let
    closure : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0 ←
    (pure
    (fun _ => (do
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _ ← (pure
    (← Core.Mem.drop
        Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
        closure));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__closure_unit_return.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__closure_unit_return.explicit_unit
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__closure_unit_return.implicit_unit
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk