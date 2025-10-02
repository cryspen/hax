
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

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.do_stuff
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a.dense_b.dense_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.do_stuff
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a.dense_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a.dense_b.dense_c
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a.dense_b.dense_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a.dense_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a.dense_b
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.do_stuff
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b.sparse_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a.sparse_b
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Off_on_sandwich.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.dense_a
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__mod.Off_on_sandwich.sparse_a
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Rustc_tests__attr__mod.Impl_.MyStruct where


def Tests.Rustc_tests__attr__mod.Impl_.Impl.off_inherit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Impl_.Impl.off_on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Impl_.Impl.off_off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Impl_.Impl_1.on_inherit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Impl_.Impl_1.on_on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Impl_.Impl_1.on_off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

class Tests.Rustc_tests__attr__mod.Impl_.MyTrait (Self : Type) where
  method : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0

instance Tests.Rustc_tests__attr__mod.Impl_.Impl_2 :
  Tests.Rustc_tests__attr__mod.Impl_.MyTrait
  Tests.Rustc_tests__attr__mod.Impl_.MyStruct
  where
  method (_ : Rust_primitives.Hax.Tuple0) := do Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Impl_.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.On.inherit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.On.on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.On.off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.Off.inherit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.Off.on
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.Off.off
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.Nested_a.Nested_b.inner
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__mod.Module.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk