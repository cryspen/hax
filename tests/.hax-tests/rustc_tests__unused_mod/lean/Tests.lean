
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

def Tests.Rustc_tests__unused_mod.Unused_module.never_called_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["I am never called
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__unused_mod.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["hello world!
"])));
  let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
  Rust_primitives.Hax.Tuple0.mk