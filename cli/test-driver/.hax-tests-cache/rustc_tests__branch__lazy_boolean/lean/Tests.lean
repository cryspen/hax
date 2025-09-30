
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

def Tests.Rustc_tests__branch__lazy_boolean.branch_and
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

def Tests.Rustc_tests__branch__lazy_boolean.branch_or
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

def Tests.Rustc_tests__branch__lazy_boolean.chain
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

def Tests.Rustc_tests__branch__lazy_boolean.nested_mixed
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

def Tests.Rustc_tests__branch__lazy_boolean.main
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
 let _: tuple0 = { tests::rustc_tests__branch__lazy_boolean::chain(x) };
 {
 let _: t...")
    Rust_primitives.Hax.Tuple0.mk)