
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

def Tests.Rustc_tests__while.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  let num : i32 ← (pure (9 : i32));
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
 while rust_primitives::hax::machine_int::ge(num, 10) {
 Tuple0
 }
 }")
    Rust_primitives.Hax.Tuple0.mk)