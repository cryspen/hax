
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

class Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T1
  (Self : Type)
  where
  f : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T2
  (Self : Type)
  where
  f : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T3
  (Self : Type)
  where
  f : Self -> Result usize

instance Tests.Legacy__lean_tests__src__traits.Overlapping_methods.Impl :
  Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T1 u32
  where
  f (self : u32) := do (0 : usize)

instance Tests.Legacy__lean_tests__src__traits.Overlapping_methods.Impl_1 :
  Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T2 u32
  where
  f (self : u32) := do (1 : usize)

instance Tests.Legacy__lean_tests__src__traits.Overlapping_methods.Impl_2 :
  Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T3 u32
  where
  f (self : u32) := do (2 : usize)

def Tests.Legacy__lean_tests__src__traits.Overlapping_methods.test
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  let x ← (pure (9 : u32));
  (← (← (← Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T1.f x)
      +? (← Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T2.f x))
    +? (← Tests.Legacy__lean_tests__src__traits.Overlapping_methods.T3.f x))

class Tests.Legacy__lean_tests__src__traits.Inheritance.T1 (Self : Type) where
  f1 : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Inheritance.T2 (Self : Type) where
  f2 : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Inheritance.T3 (Self : Type) where
  [_constr_14532845217727097520 :
  (Tests.Legacy__lean_tests__src__traits.Inheritance.T2 Self)]
  [_constr_2114861130552284825 :
  (Tests.Legacy__lean_tests__src__traits.Inheritance.T1 Self)]
  f3 : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Inheritance.Tp1 (Self : Type) where
  f1 : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Inheritance.Tp2 (Self : Type) where
  [_constr_7246171114968587502 :
  (Tests.Legacy__lean_tests__src__traits.Inheritance.Tp1 Self)]
  [_constr_1694037584750878299 :
  (Tests.Legacy__lean_tests__src__traits.Inheritance.T3 Self)]
  fp2 : Self -> Result usize

structure Tests.Legacy__lean_tests__src__traits.Inheritance.S where


instance Tests.Legacy__lean_tests__src__traits.Inheritance.Impl :
  Tests.Legacy__lean_tests__src__traits.Inheritance.T1
  Tests.Legacy__lean_tests__src__traits.Inheritance.S
  where
  f1 (self : Tests.Legacy__lean_tests__src__traits.Inheritance.S) := do
    (1 : usize)

instance Tests.Legacy__lean_tests__src__traits.Inheritance.Impl_1 :
  Tests.Legacy__lean_tests__src__traits.Inheritance.T2
  Tests.Legacy__lean_tests__src__traits.Inheritance.S
  where
  f2 (self : Tests.Legacy__lean_tests__src__traits.Inheritance.S) := do
    (2 : usize)

instance Tests.Legacy__lean_tests__src__traits.Inheritance.Impl_2 :
  Tests.Legacy__lean_tests__src__traits.Inheritance.T3
  Tests.Legacy__lean_tests__src__traits.Inheritance.S
  where
  f3 (self : Tests.Legacy__lean_tests__src__traits.Inheritance.S) := do
    (3 : usize)

instance Tests.Legacy__lean_tests__src__traits.Inheritance.Impl_3 :
  Tests.Legacy__lean_tests__src__traits.Inheritance.Tp1
  Tests.Legacy__lean_tests__src__traits.Inheritance.S
  where
  f1 (self : Tests.Legacy__lean_tests__src__traits.Inheritance.S) := do
    (10 : usize)

instance Tests.Legacy__lean_tests__src__traits.Inheritance.Impl_4 :
  Tests.Legacy__lean_tests__src__traits.Inheritance.Tp2
  Tests.Legacy__lean_tests__src__traits.Inheritance.S
  where
  fp2 (self : Tests.Legacy__lean_tests__src__traits.Inheritance.S) := do
    (← (← (← (← Tests.Legacy__lean_tests__src__traits.Inheritance.Tp1.f1 self)
          +? (← Tests.Legacy__lean_tests__src__traits.Inheritance.T1.f1 self))
        +? (← Tests.Legacy__lean_tests__src__traits.Inheritance.T2.f2 self))
      +? (← Tests.Legacy__lean_tests__src__traits.Inheritance.T3.f3 self))

def Tests.Legacy__lean_tests__src__traits.Inheritance.test
  (_ : Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  let s : Tests.Legacy__lean_tests__src__traits.Inheritance.S ← (pure
    Tests.Legacy__lean_tests__src__traits.Inheritance.S.mk);
  (← (← Tests.Legacy__lean_tests__src__traits.Inheritance.T3.f3 s)
    +? (1 : usize))

class Tests.Legacy__lean_tests__src__traits.Bounds.T1 (Self : Type) where
  f1 : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Bounds.T2 (Self : Type) where
  f2 : Self -> Result usize

class Tests.Legacy__lean_tests__src__traits.Bounds.Test
  (Self : Type) (T : Type)
  where
  [_constr_11310229916574720283 :
  (Tests.Legacy__lean_tests__src__traits.Bounds.T2 Self)]
  [_constr_10960389684919309101 :
  (Tests.Legacy__lean_tests__src__traits.Bounds.T1 T)]
  f_test : Self -> T -> Result usize

structure Tests.Legacy__lean_tests__src__traits.Bounds.S1 where


instance Tests.Legacy__lean_tests__src__traits.Bounds.Impl :
  Tests.Legacy__lean_tests__src__traits.Bounds.T1
  Tests.Legacy__lean_tests__src__traits.Bounds.S1
  where
  f1 (self : Tests.Legacy__lean_tests__src__traits.Bounds.S1) := do (0 : usize)

structure Tests.Legacy__lean_tests__src__traits.Bounds.S2 where


instance Tests.Legacy__lean_tests__src__traits.Bounds.Impl_1 :
  Tests.Legacy__lean_tests__src__traits.Bounds.T2
  Tests.Legacy__lean_tests__src__traits.Bounds.S2
  where
  f2 (self : Tests.Legacy__lean_tests__src__traits.Bounds.S2) := do (1 : usize)

instance Tests.Legacy__lean_tests__src__traits.Bounds.Impl_2 :
  Tests.Legacy__lean_tests__src__traits.Bounds.Test
  Tests.Legacy__lean_tests__src__traits.Bounds.S2
  Tests.Legacy__lean_tests__src__traits.Bounds.S1
  where
  f_test (self : Tests.Legacy__lean_tests__src__traits.Bounds.S2)
    (x : Tests.Legacy__lean_tests__src__traits.Bounds.S1)
    := do
    (← (← (← Tests.Legacy__lean_tests__src__traits.Bounds.T1.f1 x)
        +? (← Tests.Legacy__lean_tests__src__traits.Bounds.T2.f2 self))
      +? (1 : usize))

def Tests.Legacy__lean_tests__src__traits.Bounds.test
  (x1 : Tests.Legacy__lean_tests__src__traits.Bounds.S1)
  (x2 : Tests.Legacy__lean_tests__src__traits.Bounds.S2)
  : Result usize
  := do
  (← (← Tests.Legacy__lean_tests__src__traits.Bounds.Test.f_test x2 x1)
    +? (← Tests.Legacy__lean_tests__src__traits.Bounds.T1.f1 x1))

class Tests.Legacy__lean_tests__src__traits.Basic.T1 (Self : Type) where
  f1 : Self -> Result usize
  f2 : Self -> Self -> Result usize

structure Tests.Legacy__lean_tests__src__traits.Basic.S where


instance Tests.Legacy__lean_tests__src__traits.Basic.Impl :
  Tests.Legacy__lean_tests__src__traits.Basic.T1
  Tests.Legacy__lean_tests__src__traits.Basic.S
  where
  f1 (self : Tests.Legacy__lean_tests__src__traits.Basic.S) := do (42 : usize)
  f2 (self : Tests.Legacy__lean_tests__src__traits.Basic.S)
    (other : Tests.Legacy__lean_tests__src__traits.Basic.S)
    := do
    (43 : usize)

def Tests.Legacy__lean_tests__src__traits.Basic.f
  (T : Type) [(Tests.Legacy__lean_tests__src__traits.Basic.T1 T)] (x : T)
  : Result usize
  := do
  (← (← Tests.Legacy__lean_tests__src__traits.Basic.T1.f1 x)
    +? (← Tests.Legacy__lean_tests__src__traits.Basic.T1.f2 x x))

class Tests.Legacy__lean_tests__src__traits.Associated_types.Foo
  (Self : Type) (T : Type)
  where


class Tests.Legacy__lean_tests__src__traits.Associated_types.Bar
  (Self : Type)
  where


structure Tests.Legacy__lean_tests__src__traits.Associated_types.S where


instance Tests.Legacy__lean_tests__src__traits.Associated_types.Impl_2 :
  Tests.Legacy__lean_tests__src__traits.Associated_types.Bar i16
  where


instance Tests.Legacy__lean_tests__src__traits.Associated_types.Impl_3
  (A : Type) :
  Tests.Legacy__lean_tests__src__traits.Associated_types.Foo
  (Rust_primitives.Hax.Tuple2 u32 A)
  i16
  where


class Tests.Legacy__lean_tests__src__traits.Associated_types.T1
  (Self : Type)
  where
  T : Type
  f : Self -> T -> Result T

class Tests.Legacy__lean_tests__src__traits.Associated_types.T3
  (Self : Type)
  where
  T : Type
  [_constr_3149366347871078545 :
    (Tests.Legacy__lean_tests__src__traits.Associated_types.Bar T)]
  Tp : Type
  [_constr_4283472258285251198 :
    (Tests.Legacy__lean_tests__src__traits.Associated_types.Foo Tp T)]
  f (A : Type)
    [(Tests.Legacy__lean_tests__src__traits.Associated_types.Bar A)]
    :
    Self -> T -> Tp -> Result usize

instance Tests.Legacy__lean_tests__src__traits.Associated_types.Impl :
  Tests.Legacy__lean_tests__src__traits.Associated_types.T1
  Tests.Legacy__lean_tests__src__traits.Associated_types.S
  where
  T := i32
  f (self : Tests.Legacy__lean_tests__src__traits.Associated_types.S)
    (x : i32)
    := do
    (2121 : i32)

class Tests.Legacy__lean_tests__src__traits.Associated_types.T2
  (Self : Type)
  where
  T : Type
  [_constr_2524289070217738876 :
    (Tests.Legacy__lean_tests__src__traits.Associated_types.T1 T)]
  f : Self -> T -> Result usize

instance Tests.Legacy__lean_tests__src__traits.Associated_types.Impl_1 :
  Tests.Legacy__lean_tests__src__traits.Associated_types.T2
  Tests.Legacy__lean_tests__src__traits.Associated_types.S
  where
  T := Tests.Legacy__lean_tests__src__traits.Associated_types.S
  f (self : Tests.Legacy__lean_tests__src__traits.Associated_types.S)
    (x : Tests.Legacy__lean_tests__src__traits.Associated_types.S)
    := do
    (21 : usize)