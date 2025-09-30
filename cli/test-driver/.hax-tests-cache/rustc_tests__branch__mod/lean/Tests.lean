
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

def Tests.Rustc_tests__branch__mod.While_.while_cond
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

def Tests.Rustc_tests__branch__mod.While_.while_cond_not
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

def Tests.Rustc_tests__branch__mod.While_.while_op_and
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

def Tests.Rustc_tests__branch__mod.While_.while_op_or
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

def Tests.Rustc_tests__branch__mod.While_.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.While_.while_cond
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.While_.while_cond_not
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.While_.while_op_and
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.While_.while_op_or
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.No_mir_spans.while_cond
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

def Tests.Rustc_tests__branch__mod.No_mir_spans.while_cond_not
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

def Tests.Rustc_tests__branch__mod.No_mir_spans.while_op_and
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

def Tests.Rustc_tests__branch__mod.No_mir_spans.while_op_or
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

def Tests.Rustc_tests__branch__mod.No_mir_spans.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.No_mir_spans.while_cond
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.No_mir_spans.while_cond_not
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.No_mir_spans.while_op_and
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.No_mir_spans.while_op_or
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

inductive Tests.Rustc_tests__branch__mod.Match_trivial.Uninhabited : Type


def Tests.Rustc_tests__branch__mod.Match_trivial.Uninhabited
  (x : Tests.Rustc_tests__branch__mod.Match_trivial.Uninhabited)
  : Result Rust_primitives.Hax.Never
  := do
  (match x with )

inductive Tests.Rustc_tests__branch__mod.Match_trivial.Trivial : Type
| Value : Tests.Rustc_tests__branch__mod.Match_trivial.Trivial 


def Tests.Rustc_tests__branch__mod.Match_trivial.Trivial
  (x : Tests.Rustc_tests__branch__mod.Match_trivial.Trivial)
  : Result isize
  := do
  (match x with
    | (Tests.Rustc_tests__branch__mod.Match_trivial.Trivial.Value )
      => do (0 : isize))

def Tests.Rustc_tests__branch__mod.Match_trivial.consume
  (T : Type) (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box T x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Match_trivial._uninhabited
  (x : Tests.Rustc_tests__branch__mod.Match_trivial.Uninhabited)
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
      (← Tests.Rustc_tests__branch__mod.Match_trivial.consume String "done"))

def Tests.Rustc_tests__branch__mod.Match_trivial.trivial
  (x : Tests.Rustc_tests__branch__mod.Match_trivial.Trivial)
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
      | (Tests.Rustc_tests__branch__mod.Match_trivial.Trivial.Value )
        => do
          (← Tests.Rustc_tests__branch__mod.Match_trivial.consume String
              "trivial")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Match_trivial.consume String "done"));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Match_trivial.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Match_trivial.trivial
        Tests.Rustc_tests__branch__mod.Match_trivial.Trivial.Value));
  Rust_primitives.Hax.Tuple0.mk

inductive Tests.Rustc_tests__branch__mod.Match_arms.Enum : Type
| A : u32 -> Tests.Rustc_tests__branch__mod.Match_arms.Enum 
| B : u32 -> Tests.Rustc_tests__branch__mod.Match_arms.Enum 
| C : u32 -> Tests.Rustc_tests__branch__mod.Match_arms.Enum 
| D : u32 -> Tests.Rustc_tests__branch__mod.Match_arms.Enum 


instance Tests.Rustc_tests__branch__mod.Match_arms.Impl :
  Core.Clone.Clone Tests.Rustc_tests__branch__mod.Match_arms.Enum
  where


instance Tests.Rustc_tests__branch__mod.Match_arms.Impl_1 :
  Core.Marker.Copy Tests.Rustc_tests__branch__mod.Match_arms.Enum
  where


instance Tests.Rustc_tests__branch__mod.Match_arms.Impl_2 :
  Core.Fmt.Debug Tests.Rustc_tests__branch__mod.Match_arms.Enum
  where


def Tests.Rustc_tests__branch__mod.Match_arms.consume
  (T : Type) (x : T)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box T x));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Match_arms.match_arms
  (value : Tests.Rustc_tests__branch__mod.Match_arms.Enum)
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
      | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.D d)
        => do (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 d)
      | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.C c)
        => do (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 c)
      | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.B b)
        => do (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 b)
      | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.A a)
        => do (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 a)));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Match_arms.consume i32 (0 : i32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Match_arms.or_patterns
  (value : Tests.Rustc_tests__branch__mod.Match_arms.Enum)
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
      | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.D x) |
        (Tests.Rustc_tests__branch__mod.Match_arms.Enum.C x)
        => do (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 x)
      | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.B y) |
        (Tests.Rustc_tests__branch__mod.Match_arms.Enum.A y)
        => do (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 y)));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Match_arms.consume i32 (0 : i32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Match_arms.guards
  (value : Tests.Rustc_tests__branch__mod.Match_arms.Enum)
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
        | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.D d)
          => do
            (match cond with
              | TODO_LINE_622
                => do
                  (Core.Option.Option.Some
                    (← Tests.Rustc_tests__branch__mod.Match_arms.consume u32 d))
              | _ => do Core.Option.Option.None)
        | _ => do Core.Option.Option.None)
    with
      | (Core.Option.Option.Some x) => do x
      | (Core.Option.Option.None )
        => do
          (match
            (match value with
              | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.C c)
                => do
                  (match cond with
                    | TODO_LINE_622
                      => do
                        (Core.Option.Option.Some
                          (← Tests.Rustc_tests__branch__mod.Match_arms.consume
                              u32 c))
                    | _ => do Core.Option.Option.None)
              | _ => do Core.Option.Option.None)
          with
            | (Core.Option.Option.Some x) => do x
            | (Core.Option.Option.None )
              => do
                (match
                  (match value with
                    | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.B b)
                      => do
                        (match cond with
                          | TODO_LINE_622
                            => do
                              (Core.Option.Option.Some
                                (← Tests.Rustc_tests__branch__mod.Match_arms.consume
                                    u32 b))
                          | _ => do Core.Option.Option.None)
                    | _ => do Core.Option.Option.None)
                with
                  | (Core.Option.Option.Some x) => do x
                  | (Core.Option.Option.None )
                    => do
                      (match
                        (match value with
                          | (Tests.Rustc_tests__branch__mod.Match_arms.Enum.A a)
                            => do
                              (match cond with
                                | TODO_LINE_622
                                  => do
                                    (Core.Option.Option.Some
                                      (← Tests.Rustc_tests__branch__mod.Match_arms.consume
                                          u32 a))
                                | _ => do Core.Option.Option.None)
                          | _ => do Core.Option.Option.None)
                      with
                        | (Core.Option.Option.Some x) => do x
                        | (Core.Option.Option.None )
                          => do
                            (← Tests.Rustc_tests__branch__mod.Match_arms.consume
                                i32 (0 : i32)))))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Match_arms.consume i32 (0 : i32)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Match_arms.main.call_everything
  (e : Tests.Rustc_tests__branch__mod.Match_arms.Enum)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  let _ ← (pure (← Tests.Rustc_tests__branch__mod.Match_arms.match_arms e));
  let _ ← (pure (← Tests.Rustc_tests__branch__mod.Match_arms.or_patterns e));
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
 tests::rustc_tests__branch__mod::match_arms::guards(e, cond)
 }
 }")
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.Match_arms.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
    Rust_primitives.Hax.Tuple0)
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Match_arms.main.call_everything
        (Tests.Rustc_tests__branch__mod.Match_arms.Enum.A (0 : u32))));
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
 tests::rustc_tests__branch__mod::match_arms::main__call_everything(
 tests::rustc_tests_..."));
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
 tests::rustc_tests__branch__mod::match_arms::main__call_everything(
 tests::rustc_tests_..."));
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
 tests::rustc_tests__branch__mod::match_arms::main__call_everything(
 tests::rustc_tests_...")
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.Let_else.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Let_else.let_else
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
        let _ ← (pure (← Tests.Rustc_tests__branch__mod.Let_else.say x));
        Rust_primitives.Hax.Tuple0.mk
    | _
      => do
        let _ ← (pure (← Tests.Rustc_tests__branch__mod.Let_else.say "none"));
        Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.Let_else.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Let_else.let_else
        (Core.Option.Option.Some "x")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Let_else.let_else
        (Core.Option.Option.Some "x")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Let_else.let_else
        Core.Option.Option.None));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.If_.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.If_.branch_not
  (a : Bool)
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
    (← if a then do
      (← Tests.Rustc_tests__branch__mod.If_.say "a")
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Ops.Bit.Not.not a) then do
      let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "not a"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)) then do
      let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "not not a"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  (← if
  (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)))
  then do
    let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "not not not a"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.If_.branch_not_as
  (a : Bool)
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
    (← if (← Core.Ops.Bit.Not.not a) then do
      let _ ← (pure
        (← Tests.Rustc_tests__branch__mod.If_.say "not (a as bool)"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)) then do
      let _ ← (pure
        (← Tests.Rustc_tests__branch__mod.If_.say "not not (a as bool)"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  (← if
  (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)))
  then do
    let _ ← (pure
      (← Tests.Rustc_tests__branch__mod.If_.say "not not (a as bool)"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.If_.branch_and
  (a : Bool)
  (b : Bool)
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
  (← if (← a &&? b) then do
    let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "both"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "not both"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.If_.branch_or
  (a : Bool)
  (b : Bool)
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
  (← if (← a ||? b) then do
    let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "either"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__branch__mod.If_.say "neither"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.If_.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
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
 for a in (core::iter::traits::collect::f_into_iter([false, true, true])) {
 {
 let _: tuple0 = { tests::rustc_tests__branch__mod::if_::branch_not(a) };
 {
 let _: tuple0 = {
 tests::rustc_tests__br..."));
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
 for a in (core::iter::traits::collect::f_into_iter([
 false, true, true, true, true,
 ])) {
 {
 for b in (core::iter::traits::collect::f_into_iter([
 false, true, true,
 ])) {
 {
 let _: tuple0 = {...")
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.Guard.branch_match_guard
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

def Tests.Rustc_tests__branch__mod.Guard.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Guard.branch_match_guard
        (Core.Option.Option.Some (0 : u32))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Guard.branch_match_guard
        (Core.Option.Option.Some (2 : u32))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Guard.branch_match_guard
        (Core.Option.Option.Some (6 : u32))));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Guard.branch_match_guard
        (Core.Option.Option.Some (3 : u32))));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Generics.print_size
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← if
  (← Rust_primitives.Hax.Machine_int.gt
      (← Core.Mem.size_of T Rust_primitives.Hax.Tuple0.mk)
      (4 : usize)) then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["size > 4
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize) #v["size <= 4
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__mod.Generics.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Generics.print_size
        Rust_primitives.Hax.Tuple0 Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Generics.print_size u32
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__mod.Generics.print_size u64
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Lazy_boolean.branch_and
  (a : Bool)
  (b : Bool)
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
  let c : Bool ← (pure (← a &&? b));
  let _ ← (pure (← Core.Hint.black_box Bool c));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Lazy_boolean.branch_or
  (a : Bool)
  (b : Bool)
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
  let c : Bool ← (pure (← a ||? b));
  let _ ← (pure (← Core.Hint.black_box Bool c));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Lazy_boolean.chain
  (x : u32)
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
  let c : Bool ← (pure
    (← (← (← (← Rust_primitives.Hax.Machine_int.gt x (1 : u32))
          &&? (← Rust_primitives.Hax.Machine_int.gt x (2 : u32)))
        &&? (← Rust_primitives.Hax.Machine_int.gt x (4 : u32)))
      &&? (← Rust_primitives.Hax.Machine_int.gt x (8 : u32))));
  let _ ← (pure (← Core.Hint.black_box Bool c));
  let d : Bool ← (pure
    (← (← (← (← Rust_primitives.Hax.Machine_int.lt x (1 : u32))
          ||? (← Rust_primitives.Hax.Machine_int.lt x (2 : u32)))
        ||? (← Rust_primitives.Hax.Machine_int.lt x (4 : u32)))
      ||? (← Rust_primitives.Hax.Machine_int.lt x (8 : u32))));
  let _ ← (pure (← Core.Hint.black_box Bool d));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Lazy_boolean.nested_mixed
  (x : u32)
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
  let c : Bool ← (pure
    (← (← (← Rust_primitives.Hax.Machine_int.lt x (4 : u32))
        ||? (← Rust_primitives.Hax.Machine_int.ge x (9 : u32)))
      &&? (← (← Rust_primitives.Hax.Machine_int.lt x (2 : u32))
        ||? (← Rust_primitives.Hax.Machine_int.ge x (10 : u32)))));
  let _ ← (pure (← Core.Hint.black_box Bool c));
  let d : Bool ← (pure
    (← (← (← Rust_primitives.Hax.Machine_int.lt x (4 : u32))
        &&? (← Rust_primitives.Hax.Machine_int.lt x (1 : u32)))
      ||? (← (← Rust_primitives.Hax.Machine_int.ge x (8 : u32))
        &&? (← Rust_primitives.Hax.Machine_int.ge x (10 : u32)))));
  let _ ← (pure (← Core.Hint.black_box Bool d));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__mod.Lazy_boolean.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Rust_primitives.Hax.Tuple2
    Rust_primitives.Hax.Tuple0
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
 for a in (core::iter::traits::collect::f_into_iter([
 false, true, true, true, true,
 ])) {
 {
 for b in (core::iter::traits::collect::f_into_iter([
 false, true, true,
 ])) {
 {
 let _: tuple0 = {..."));
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
 for x in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {
 f_start: 0,
 f_end: 16,
 })) {
 {
 let _: tuple0 = {
 tests::rustc_tests__branch__mod::lazy_boolean::chain(x)
 };
 {
 l...")
    Rust_primitives.Hax.Tuple0.mk)