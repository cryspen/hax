
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

def Tests.Rustc_tests__branch__no_mir_spans.while_cond
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
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
  let a : i32 ← (pure (8 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun a => (do
            (← Rust_primitives.Hax.Machine_int.gt a (0 : i32)) : Result Bool))
        (fun a => (do true : Result Bool))
        (fun a => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        a
        (fun a => (do let a : i32 ← (pure (← a -? (1 : i32))); a : Result i32)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__no_mir_spans.while_cond_not
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Rust_primitives.Hax.Tuple2 i32 Rust_primitives.Hax.Tuple0)
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
  let a : i32 ← (pure (8 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun a => (do
            (← Core.Ops.Bit.Not.not
                (← Rust_primitives.Hax.Machine_int.eq a (0 : i32))) : Result
            Bool))
        (fun a => (do true : Result Bool))
        (fun a => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        a
        (fun a => (do let a : i32 ← (pure (← a -? (1 : i32))); a : Result i32)))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__no_mir_spans.while_op_and
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    (Rust_primitives.Hax.Tuple2 i32 i32)
    Rust_primitives.Hax.Tuple0)
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
  let a : i32 ← (pure (8 : i32));
  let b : i32 ← (pure (4 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun ⟨a, b⟩ => (do
            (← (← Rust_primitives.Hax.Machine_int.gt a (0 : i32))
              &&? (← Rust_primitives.Hax.Machine_int.gt b (0 : i32))) : Result
            Bool))
        (fun ⟨a, b⟩ => (do true : Result Bool))
        (fun ⟨a, b⟩ => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple2.mk a b)
        (fun ⟨a, b⟩ => (do
            let a : i32 ← (pure (← a -? (1 : i32)));
            let b : i32 ← (pure (← b -? (1 : i32)));
            (Rust_primitives.Hax.Tuple2.mk a b) : Result
            (Rust_primitives.Hax.Tuple2 i32 i32))))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__no_mir_spans.while_op_or
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    (Rust_primitives.Hax.Tuple2 i32 i32)
    Rust_primitives.Hax.Tuple0)
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
  let a : i32 ← (pure (4 : i32));
  let b : i32 ← (pure (8 : i32));
  (Rust_primitives.Hax.Tuple2.mk
    (← Rust_primitives.Hax.while_loop
        (fun ⟨a, b⟩ => (do
            (← (← Rust_primitives.Hax.Machine_int.gt a (0 : i32))
              ||? (← Rust_primitives.Hax.Machine_int.gt b (0 : i32))) : Result
            Bool))
        (fun ⟨a, b⟩ => (do true : Result Bool))
        (fun ⟨a, b⟩ => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple2.mk a b)
        (fun ⟨a, b⟩ => (do
            let a : i32 ← (pure (← a -? (1 : i32)));
            let b : i32 ← (pure (← b -? (1 : i32)));
            (Rust_primitives.Hax.Tuple2.mk a b) : Result
            (Rust_primitives.Hax.Tuple2 i32 i32))))
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__no_mir_spans.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__no_mir_spans.while_cond
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__no_mir_spans.while_cond_not
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__no_mir_spans.while_op_and
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__no_mir_spans.while_op_or
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk