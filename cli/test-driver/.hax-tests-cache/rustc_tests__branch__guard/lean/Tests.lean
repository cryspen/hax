
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

def Tests.Rustc_tests__branch__guard.branch_match_guard
  (x : (Core.Option.Option u32))
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
  (match x with
    | (Core.Option.Option.Some TODO_LINE_622)
      => do
        let _ ← (pure
          (← Std.Io.Stdio._print
              (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["zero
"])));
        let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
        Rust_primitives.Hax.Tuple0.mk
    | _
      => do
        (match
          (match x with
            | (Core.Option.Option.Some x)
              => do
                (match
                  (← Rust_primitives.Hax.Machine_int.eq
                      (← x %? (2 : u32))
                      (0 : u32))
                with
                  | TODO_LINE_622
                    => do
                      let _ ← (pure
                        (← Std.Io.Stdio._print
                            (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                                #v["is nonzero and even
"])));
                      let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                      (Core.Option.Option.Some Rust_primitives.Hax.Tuple0.mk)
                  | _ => do Core.Option.Option.None)
            | _ => do Core.Option.Option.None)
        with
          | (Core.Option.Option.Some x) => do x
          | (Core.Option.Option.None )
            => do
              (match
                (match x with
                  | (Core.Option.Option.Some x)
                    => do
                      (match
                        (← Rust_primitives.Hax.Machine_int.eq
                            (← x %? (3 : u32))
                            (0 : u32))
                      with
                        | TODO_LINE_622
                          => do
                            let _ ← (pure
                              (← Std.Io.Stdio._print
                                  (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                                      #v["is nonzero and odd, but divisible by 3
"])));
                            let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                            (Core.Option.Option.Some
                              Rust_primitives.Hax.Tuple0.mk)
                        | _ => do Core.Option.Option.None)
                  | _ => do Core.Option.Option.None)
              with
                | (Core.Option.Option.Some x) => do x
                | (Core.Option.Option.None )
                  => do
                    let _ ← (pure
                      (← Std.Io.Stdio._print
                          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
                              #v["something else
"])));
                    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
                    Rust_primitives.Hax.Tuple0.mk)))

def Tests.Rustc_tests__branch__guard.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__guard.branch_match_guard
        (Core.Option.Option.Some (0 : u32))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__guard.branch_match_guard
        (Core.Option.Option.Some (2 : u32))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__guard.branch_match_guard
        (Core.Option.Option.Some (6 : u32))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__guard.branch_match_guard
        (Core.Option.Option.Some (3 : u32))));
  Rust_primitives.Hax.Tuple0.mk