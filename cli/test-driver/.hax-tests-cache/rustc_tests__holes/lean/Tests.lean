
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

def Tests.Rustc_tests__holes.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
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

def Tests.Rustc_tests__holes.main.MY_STATIC
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__holes.main.MY_CONST
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__holes.main._unused_fn
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Rustc_tests__holes.main.MyStruct where
  _x : u32
  _y : u32

def Tests.Rustc_tests__holes.main.Impl._method
  (self : Tests.Rustc_tests__holes.main.MyStruct)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

class Tests.Rustc_tests__holes.main.MyTrait (Self : Type) where


instance Tests.Rustc_tests__holes.main.Impl_1 :
  Tests.Rustc_tests__holes.main.MyTrait Tests.Rustc_tests__holes.main.MyStruct
  where
  