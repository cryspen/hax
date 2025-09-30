
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

structure Tests.Rustc_tests__attr__impl.MyStruct where


def Tests.Rustc_tests__attr__impl.Impl.off_inherit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__impl.Impl.off_on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__impl.Impl.off_off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__impl.Impl_1.on_inherit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__impl.Impl_1.on_on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__impl.Impl_1.on_off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

class Tests.Rustc_tests__attr__impl.MyTrait (Self : Type) where
  method : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0

instance Tests.Rustc_tests__attr__impl.Impl_2 :
  Tests.Rustc_tests__attr__impl.MyTrait Tests.Rustc_tests__attr__impl.MyStruct
  where
  method (_ : Rust_primitives.Hax.Tuple0) := do Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__impl.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk