
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

def Tests.Rustc_tests__mcdc__condition_limit.accept_7_conditions
  (bool_arr : (RustArray Bool (7 : usize)))
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.failure
      "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/804.
Please upvote or comment this issue if you see this error message.
Pat:Array

This is discussed in issue https://github.com/hacspec/hax/issues/804.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `AST import`.
"
      "")

def Tests.Rustc_tests__mcdc__condition_limit.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__condition_limit.accept_7_conditions
        (← Rust_primitives.Hax.repeat false (7 : usize))));
  let _ ← (pure
    (← Tests.Rustc_tests__mcdc__condition_limit.accept_7_conditions
        (← Rust_primitives.Hax.repeat true (7 : usize))));
  Rust_primitives.Hax.Tuple0.mk