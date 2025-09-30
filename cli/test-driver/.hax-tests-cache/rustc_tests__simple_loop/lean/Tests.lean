
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

def Tests.Rustc_tests__simple_loop.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
  := do
  let is_true : Bool ← (pure
    (← Rust_primitives.Hax.Machine_int.eq
        (← Core.Iter.Traits.Exact_size.ExactSizeIterator.len
            (← Std.Env.args Rust_primitives.Hax.Tuple0.mk))
        (1 : usize)));
  let countdown : i32 ← (pure (0 : i32));
  let countdown : i32 ← (pure
    (← if is_true then do
      let countdown : i32 ← (pure (10 : i32));
      countdown
    else do
      countdown));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.failure
        "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/933.
Please upvote or comment this issue if you see this error message.
Unhandled loop kind

This is discussed in issue https://github.com/hacspec/hax/issues/933.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `FunctionalizeLoops`.
"
        "{
 (loop {
 |countdown| {
 (if rust_primitives::hax::machine_int::eq(countdown, 0) {
 core::ops::control_flow::ControlFlow_Break(Tuple2(Tuple0, countdown))
 } else {
 core::ops::control_flow::ControlF...")
    Rust_primitives.Hax.Tuple0.mk)