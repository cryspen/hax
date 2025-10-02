
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

def Tests.Rustc_tests__simple_match.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : i32 ← (pure (1 : i32));
  let countdown : i32 ← (pure
    (← if is_true then do
      let countdown : i32 ← (pure (0 : i32));
      countdown
    else do
      countdown));
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
 for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {
 f_start: 0,
 f_end: 2,
 })) {
 rust_primitives::hax::failure(
 "something is not implemented yet.This is discussed in i...")
    Rust_primitives.Hax.Tuple0.mk)