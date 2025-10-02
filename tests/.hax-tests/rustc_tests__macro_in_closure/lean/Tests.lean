
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

def Tests.Rustc_tests__macro_in_closure.NO_BLOCK
  : Result Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
  := do
  (fun _ => (do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["hello
"])));
      Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0))

def Tests.Rustc_tests__macro_in_closure.WITH_BLOCK
  : Result Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0
  := do
  (fun _ => (do
      let _ ← (pure
        (← Std.Io.Stdio._print
            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["hello
"])));
      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
      Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0))

def Tests.Rustc_tests__macro_in_closure.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__macro_in_closure.NO_BLOCK
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__macro_in_closure.WITH_BLOCK
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk