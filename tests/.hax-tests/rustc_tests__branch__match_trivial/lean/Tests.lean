
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

inductive Tests.Rustc_tests__branch__match_trivial.Uninhabited : Type


def Tests.Rustc_tests__branch__match_trivial.Uninhabited
  (x : Tests.Rustc_tests__branch__match_trivial.Uninhabited)
  : Result Rust_primitives.Hax.Never
  := do
  (match x with )

inductive Tests.Rustc_tests__branch__match_trivial.Trivial : Type
| Value : Tests.Rustc_tests__branch__match_trivial.Trivial 


def Tests.Rustc_tests__branch__match_trivial.Trivial
  (x : Tests.Rustc_tests__branch__match_trivial.Trivial)
  : Result isize
  := do
  (match x with
    | (Tests.Rustc_tests__branch__match_trivial.Trivial.Value )
      => do (0 : isize))

def Tests.Rustc_tests__branch__match_trivial.consume
  (T : Type) (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box T x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__match_trivial._uninhabited
  (x : Tests.Rustc_tests__branch__match_trivial.Uninhabited)
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
  let _ ← (pure (← Rust_primitives.Hax.never_to_any (match x with )));
  (← Rust_primitives.Hax.never_to_any
      (← Tests.Rustc_tests__branch__match_trivial.consume String "done"))

def Tests.Rustc_tests__branch__match_trivial.trivial
  (x : Tests.Rustc_tests__branch__match_trivial.Trivial)
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
  let _ ← (pure
    (match x with
      | (Tests.Rustc_tests__branch__match_trivial.Trivial.Value )
        => do
          (← Tests.Rustc_tests__branch__match_trivial.consume String
              "trivial")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__match_trivial.consume String "done"));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__match_trivial.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__match_trivial.trivial
        Tests.Rustc_tests__branch__match_trivial.Trivial.Value));
  Rust_primitives.Hax.Tuple0.mk