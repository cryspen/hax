
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

def Tests.Rustc_tests__tight_inf_loop.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if false then do
    (← Rust_primitives.Hax.never_to_any
        (Rust_primitives.Hax.Tuple2.mk
          (← Rust_primitives.Hax.failure
              "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Loop without mutation

This is discussed in issue https://github.com/hacspec/hax/issues/405.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
              "{
 loop {
 Tuple0
 }
 }")
          Rust_primitives.Hax.Tuple0.mk))
  else do
    Rust_primitives.Hax.Tuple0.mk)