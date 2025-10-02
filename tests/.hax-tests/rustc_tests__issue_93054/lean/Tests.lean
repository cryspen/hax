
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

inductive Tests.Rustc_tests__issue_93054.Never : Type


def Tests.Rustc_tests__issue_93054.Never
  (x : Tests.Rustc_tests__issue_93054.Never)
  : Result Rust_primitives.Hax.Never
  := do
  (match x with )

def Tests.Rustc_tests__issue_93054.Impl.bar
  (self : Tests.Rustc_tests__issue_93054.Never)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.never_to_any (match self with ))

def Tests.Rustc_tests__issue_93054.foo2
  (never : Tests.Rustc_tests__issue_93054.Never)
  : Result Rust_primitives.Hax.failure
  := do
  (← Rust_primitives.Hax.failure
      "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Got type `Coroutine`: coroutines are not supported by hax

This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `AST import`.
"
      "")

def Tests.Rustc_tests__issue_93054.make
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Option.Option Tests.Rustc_tests__issue_93054.Never)
  := do
  Core.Option.Option.None

def Tests.Rustc_tests__issue_93054.Impl.foo
  (self : Tests.Rustc_tests__issue_93054.Never)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (← Rust_primitives.Hax.never_to_any (match self with )));
  (← Rust_primitives.Hax.never_to_any
      (← Core.Option.Impl.map
          Tests.Rustc_tests__issue_93054.Never
          Rust_primitives.Hax.Never
          Tests.Rustc_tests__issue_93054.Never
          -> Result Rust_primitives.Hax.Never
          (← Tests.Rustc_tests__issue_93054.make Rust_primitives.Hax.Tuple0.mk)
          (fun never => (do
              (match never with ) : Result Rust_primitives.Hax.Never))))

def Tests.Rustc_tests__issue_93054.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk