
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

def Tests.Rustc_tests__branch__if_let.say
  (message : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Core.Hint.black_box String message));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__if_let.if_let
  (input : (Core.Option.Option String))
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
    (match input with
      | (Core.Option.Option.Some x)
        => do
          let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say x));
          Rust_primitives.Hax.Tuple0.mk
      | _
        => do
          let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say "none"));
          Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say "done"));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__if_let.if_let_chain
  (a : (Core.Option.Option String))
  (b : (Core.Option.Option String))
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← if
    (← (← Rust_primitives.Hax.failure
          "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: `Let` nodes are supposed to be pre-processed


Note: the error was labeled with context `AST import`.
"
          "")
      &&? (← Rust_primitives.Hax.failure
          "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!
Details: `Let` nodes are supposed to be pre-processed


Note: the error was labeled with context `AST import`.
"
          "")) then do
      let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say x));
      let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say y));
      Rust_primitives.Hax.Tuple0.mk
    else do
      let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say "not both"));
      Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure (← Tests.Rustc_tests__branch__if_let.say "done"));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__branch__if_let.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__branch__if_let.if_let (Core.Option.Option.Some "x")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__if_let.if_let (Core.Option.Option.Some "x")));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__if_let.if_let Core.Option.Option.None));
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
 f_end: 8,
 })) {
 tests::rustc_tests__branch__if_let::if_let_chain(
 core::option::Option_Some("a"),
 core..."));
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
 f_end: 4,
 })) {
 tests::rustc_tests__branch__if_let::if_let_chain(
 core::option::Option_Some("a"),
 core..."));
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
 f_end: 2,
 })) {
 tests::rustc_tests__branch__if_let::if_let_chain(
 core::option::Option_None(),
 core::o..."));
  let _ ← (pure
    (← Tests.Rustc_tests__branch__if_let.if_let_chain
        Core.Option.Option.None
        Core.Option.Option.None));
  Rust_primitives.Hax.Tuple0.mk