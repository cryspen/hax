
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

def Tests.Rustc_tests__attr__nested.do_stuff
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__nested.outer_fn
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__nested.outer_fn.middle_fn
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__nested.outer_fn.middle_fn.inner_fn
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Rustc_tests__attr__nested.MyOuter where


def Tests.Rustc_tests__attr__nested.Impl.outer_method
  (self : Tests.Rustc_tests__attr__nested.MyOuter)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Rustc_tests__attr__nested.Impl.outer_method.MyMiddle where


def Tests.Rustc_tests__attr__nested.Impl.outer_method.Impl.middle_method
  (self : Tests.Rustc_tests__attr__nested.Impl.outer_method.MyMiddle)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

structure
  Tests.Rustc_tests__attr__nested.Impl.outer_method.Impl.middle_method.MyInner
  where


def
  Tests.Rustc_tests__attr__nested.Impl.outer_method.Impl.middle_method.Impl.inner_method
  (self :
  Tests.Rustc_tests__attr__nested.Impl.outer_method.Impl.middle_method.MyInner)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

class Tests.Rustc_tests__attr__nested.MyTrait (Self : Type) where
  trait_method : Self -> Result Rust_primitives.Hax.Tuple0

instance Tests.Rustc_tests__attr__nested.Impl_1 :
  Tests.Rustc_tests__attr__nested.MyTrait
  Tests.Rustc_tests__attr__nested.MyOuter
  where
  trait_method (self : Tests.Rustc_tests__attr__nested.MyOuter) := do
    let _ ← (pure
      (← Tests.Rustc_tests__attr__nested.do_stuff
          Rust_primitives.Hax.Tuple0.mk));
    Rust_primitives.Hax.Tuple0.mk

structure Tests.Rustc_tests__attr__nested.Impl_1.trait_method.MyMiddle where


instance Tests.Rustc_tests__attr__nested.Impl_1.trait_method.Impl :
  Tests.Rustc_tests__attr__nested.MyTrait
  Tests.Rustc_tests__attr__nested.Impl_1.trait_method.MyMiddle
  where
  trait_method (self :
    Tests.Rustc_tests__attr__nested.Impl_1.trait_method.MyMiddle)
    := do
    let _ ← (pure
      (← Tests.Rustc_tests__attr__nested.do_stuff
          Rust_primitives.Hax.Tuple0.mk));
    Rust_primitives.Hax.Tuple0.mk

structure
  Tests.Rustc_tests__attr__nested.Impl_1.trait_method.Impl.trait_method.MyInner
  where


instance
  Tests.Rustc_tests__attr__nested.Impl_1.trait_method.Impl.trait_method.Impl
  :
  Tests.Rustc_tests__attr__nested.MyTrait
  Tests.Rustc_tests__attr__nested.Impl_1.trait_method.Impl.trait_method.MyInner
  where
  trait_method (self :
    Tests.Rustc_tests__attr__nested.Impl_1.trait_method.Impl.trait_method.MyInner)
    := do
    let _ ← (pure
      (← Tests.Rustc_tests__attr__nested.do_stuff
          Rust_primitives.Hax.Tuple0.mk));
    Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__nested.closure_expr
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _outer : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0 ←
    (pure
    (fun _ => (do
        let
          _middle : Rust_primitives.Hax.Tuple0
          -> Result Rust_primitives.Hax.Tuple0 ← (pure
          (fun _ => (do
              let
                _inner : Rust_primitives.Hax.Tuple0
                -> Result Rust_primitives.Hax.Tuple0 ← (pure
                (fun _ => (do
                    let _ ← (pure
                      (← Tests.Rustc_tests__attr__nested.do_stuff
                          Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk : Result
                    Rust_primitives.Hax.Tuple0)));
              let _ ← (pure
                (← Tests.Rustc_tests__attr__nested.do_stuff
                    Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk : Result
              Rust_primitives.Hax.Tuple0)));
        let _ ← (pure
          (← Tests.Rustc_tests__attr__nested.do_stuff
              Rust_primitives.Hax.Tuple0.mk));
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__nested.closure_tail
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _outer : Rust_primitives.Hax.Tuple0 -> Result Rust_primitives.Hax.Tuple0 ←
    (pure
    (fun _ => (do
        let
          _middle : Rust_primitives.Hax.Tuple0
          -> Result Rust_primitives.Hax.Tuple0 ← (pure
          (fun _ => (do
              let
                _inner : Rust_primitives.Hax.Tuple0
                -> Result Rust_primitives.Hax.Tuple0 ← (pure
                (fun _ => (do
                    let _ ← (pure
                      (← Tests.Rustc_tests__attr__nested.do_stuff
                          Rust_primitives.Hax.Tuple0.mk));
                    Rust_primitives.Hax.Tuple0.mk : Result
                    Rust_primitives.Hax.Tuple0)));
              let _ ← (pure
                (← Tests.Rustc_tests__attr__nested.do_stuff
                    Rust_primitives.Hax.Tuple0.mk));
              Rust_primitives.Hax.Tuple0.mk : Result
              Rust_primitives.Hax.Tuple0)));
        let _ ← (pure
          (← Tests.Rustc_tests__attr__nested.do_stuff
              Rust_primitives.Hax.Tuple0.mk));
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.do_stuff Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__nested.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.outer_fn Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.Impl.outer_method
        Tests.Rustc_tests__attr__nested.MyOuter.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.MyTrait.trait_method
        Tests.Rustc_tests__attr__nested.MyOuter.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.closure_expr
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__nested.closure_tail
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk