
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

structure Tests.Rustc_tests__attr__trait_impl_inherit.S where


instance Tests.Rustc_tests__attr__trait_impl_inherit.Impl :
  Tests.Rustc_tests__attr__trait_impl_inherit.T
  Tests.Rustc_tests__attr__trait_impl_inherit.S
  where
  f (self : Tests.Rustc_tests__attr__trait_impl_inherit.S) := do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["impl S
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__trait_impl_inherit.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__trait_impl_inherit.T.f
        Tests.Rustc_tests__attr__trait_impl_inherit.S.mk));
  Rust_primitives.Hax.Tuple0.mk