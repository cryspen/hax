
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

def Tests.Rustc_tests__branch__let_else.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__let_else.let_else
  (value : (Core.Option.Option String))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
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
 f_end: 1,
 })) {
 Tuple0
 }
 }"));
  (match value with
    | (Core.Option.Option.Some x)
      => do
        let _ ← (pure (← Tests.Rustc_tests__branch__let_else.say x));
        Rust_primitives.Hax.Tuple0.mk
    | _
      => do
        let _ ← (pure (← Tests.Rustc_tests__branch__let_else.say "none"));
        Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__let_else.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__let_else.let_else
        (Core.Option.Option.Some "x")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__let_else.let_else
        (Core.Option.Option.Some "x")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__let_else.let_else Core.Option.Option.None));
  Rust_primitives.Hax.Tuple0.mk