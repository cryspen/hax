
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

inductive Tests.Rustc_tests__branch__match_arms.Enum : Type
| A : u32 -> Tests.Rustc_tests__branch__match_arms.Enum 
| B : u32 -> Tests.Rustc_tests__branch__match_arms.Enum 
| C : u32 -> Tests.Rustc_tests__branch__match_arms.Enum 
| D : u32 -> Tests.Rustc_tests__branch__match_arms.Enum 


instance Tests.Rustc_tests__branch__match_arms.Impl :
  Core.Clone.Clone Tests.Rustc_tests__branch__match_arms.Enum
  where


instance Tests.Rustc_tests__branch__match_arms.Impl_1 :
  Core.Marker.Copy Tests.Rustc_tests__branch__match_arms.Enum
  where


instance Tests.Rustc_tests__branch__match_arms.Impl_2 :
  Core.Fmt.Debug Tests.Rustc_tests__branch__match_arms.Enum
  where


def Tests.Rustc_tests__branch__match_arms.consume
  (T : Type) (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box T x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__match_arms.match_arms
  (value : Tests.Rustc_tests__branch__match_arms.Enum)
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
    (match value with
      | (Tests.Rustc_tests__branch__match_arms.Enum.D d)
        => do (← Tests.Rustc_tests__branch__match_arms.consume u32 d)
      | (Tests.Rustc_tests__branch__match_arms.Enum.C c)
        => do (← Tests.Rustc_tests__branch__match_arms.consume u32 c)
      | (Tests.Rustc_tests__branch__match_arms.Enum.B b)
        => do (← Tests.Rustc_tests__branch__match_arms.consume u32 b)
      | (Tests.Rustc_tests__branch__match_arms.Enum.A a)
        => do (← Tests.Rustc_tests__branch__match_arms.consume u32 a)));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__match_arms.consume i32 (0 : i32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__match_arms.or_patterns
  (value : Tests.Rustc_tests__branch__match_arms.Enum)
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
    (match value with
      | (Tests.Rustc_tests__branch__match_arms.Enum.D x) |
        (Tests.Rustc_tests__branch__match_arms.Enum.C x)
        => do (← Tests.Rustc_tests__branch__match_arms.consume u32 x)
      | (Tests.Rustc_tests__branch__match_arms.Enum.B y) |
        (Tests.Rustc_tests__branch__match_arms.Enum.A y)
        => do (← Tests.Rustc_tests__branch__match_arms.consume u32 y)));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__match_arms.consume i32 (0 : i32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__match_arms.guards
  (value : Tests.Rustc_tests__branch__match_arms.Enum)
  (cond : Bool)
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
    (match
      (match value with
        | (Tests.Rustc_tests__branch__match_arms.Enum.D d)
          => do
            (match cond with
              | TODO_LINE_622
                => do
                  (Core.Option.Option.Some
                    (← Tests.Rustc_tests__branch__match_arms.consume u32 d))
              | _ => do Core.Option.Option.None)
        | _ => do Core.Option.Option.None)
    with
      | (Core.Option.Option.Some x) => do x
      | (Core.Option.Option.None )
        => do
          (match
            (match value with
              | (Tests.Rustc_tests__branch__match_arms.Enum.C c)
                => do
                  (match cond with
                    | TODO_LINE_622
                      => do
                        (Core.Option.Option.Some
                          (← Tests.Rustc_tests__branch__match_arms.consume u32
                              c))
                    | _ => do Core.Option.Option.None)
              | _ => do Core.Option.Option.None)
          with
            | (Core.Option.Option.Some x) => do x
            | (Core.Option.Option.None )
              => do
                (match
                  (match value with
                    | (Tests.Rustc_tests__branch__match_arms.Enum.B b)
                      => do
                        (match cond with
                          | TODO_LINE_622
                            => do
                              (Core.Option.Option.Some
                                (← Tests.Rustc_tests__branch__match_arms.consume
                                    u32 b))
                          | _ => do Core.Option.Option.None)
                    | _ => do Core.Option.Option.None)
                with
                  | (Core.Option.Option.Some x) => do x
                  | (Core.Option.Option.None )
                    => do
                      (match
                        (match value with
                          | (Tests.Rustc_tests__branch__match_arms.Enum.A a)
                            => do
                              (match cond with
                                | TODO_LINE_622
                                  => do
                                    (Core.Option.Option.Some
                                      (← Tests.Rustc_tests__branch__match_arms.consume
                                          u32 a))
                                | _ => do Core.Option.Option.None)
                          | _ => do Core.Option.Option.None)
                      with
                        | (Core.Option.Option.Some x) => do x
                        | (Core.Option.Option.None )
                          => do
                            (← Tests.Rustc_tests__branch__match_arms.consume i32
                                (0 : i32)))))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__match_arms.consume i32 (0 : i32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__match_arms.main.call_everything
  (e : Tests.Rustc_tests__branch__match_arms.Enum)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  let _ ← (pure (← Tests.Rustc_tests__branch__match_arms.match_arms e));
  let _ ← (pure (← Tests.Rustc_tests__branch__match_arms.or_patterns e));
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
 for cond in (core::iter::traits::collect::f_into_iter([false, false, true])) {
 tests::rustc_tests__branch__match_arms::guards(e, cond)
 }
 }")
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__match_arms.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__match_arms.main.call_everything
        (Tests.Rustc_tests__branch__match_arms.Enum.A (0 : u32))));
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
 for b in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {
 f_start: 0,
 f_end: 2,
 })) {
 tests::rustc_tests__branch__match_arms::main__call_everything(
 tests::rustc_tests__bran..."));
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
 for c in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {
 f_start: 0,
 f_end: 4,
 })) {
 tests::rustc_tests__branch__match_arms::main__call_everything(
 tests::rustc_tests__bran..."));
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
 for d in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {
 f_start: 0,
 f_end: 8,
 })) {
 tests::rustc_tests__branch__match_arms::main__call_everything(
 tests::rustc_tests__bran...")
    Rust_primitives.Hax.Tuple0.mk)