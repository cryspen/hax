
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

def Tests.Rustc_tests__branch__if.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__if.branch_not
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
      (← Tests.Rustc_tests__branch__if.say "a")
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Ops.Bit.Not.not a) then do
      let _ ← (pure (← Tests.Rustc_tests__branch__if.say "not a"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)) then do
      let _ ← (pure (← Tests.Rustc_tests__branch__if.say "not not a"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  (← if
  (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)))
  then do
    let _ ← (pure (← Tests.Rustc_tests__branch__if.say "not not not a"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__if.branch_not_as
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
      let _ ← (pure (← Tests.Rustc_tests__branch__if.say "not (a as bool)"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← if (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)) then do
      let _ ← (pure
        (← Tests.Rustc_tests__branch__if.say "not not (a as bool)"));
      Rust_primitives.Hax.Tuple0.mk
    else do
      Rust_primitives.Hax.Tuple0.mk));
  (← if
  (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not (← Core.Ops.Bit.Not.not a)))
  then do
    let _ ← (pure (← Tests.Rustc_tests__branch__if.say "not not (a as bool)"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__if.branch_and
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
    let _ ← (pure (← Tests.Rustc_tests__branch__if.say "both"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__branch__if.say "not both"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__if.branch_or
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
    let _ ← (pure (← Tests.Rustc_tests__branch__if.say "either"));
    Rust_primitives.Hax.Tuple0.mk
  else do
    let _ ← (pure (← Tests.Rustc_tests__branch__if.say "neither"));
    Rust_primitives.Hax.Tuple0.mk)

def Tests.Rustc_tests__branch__if.main
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
 let _: tuple0 = { tests::rustc_tests__branch__if::branch_not(a) };
 {
 let _: tuple0 = { tests::rustc_tests__branch__i..."));
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