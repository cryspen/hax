
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

structure Tests.Legacy__naming.Functions_defined_in_trait_impls.A where


def
  Tests.Legacy__naming.Functions_defined_in_trait_impls.Impl.eq.panic_cold_explicit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Never
  := do
  (← Core.Panicking.panic_explicit Rust_primitives.Hax.Tuple0.mk)

instance Tests.Legacy__naming.Functions_defined_in_trait_impls.Impl :
  Core.Cmp.PartialEq
  Tests.Legacy__naming.Functions_defined_in_trait_impls.A
  Tests.Legacy__naming.Functions_defined_in_trait_impls.A
  where
  eq (self : Tests.Legacy__naming.Functions_defined_in_trait_impls.A)
    (other : Tests.Legacy__naming.Functions_defined_in_trait_impls.A)
    := do
    (← Rust_primitives.Hax.never_to_any
        (← Tests.Legacy__naming.Functions_defined_in_trait_impls.Impl.eq.panic_cold_explicit
            Rust_primitives.Hax.Tuple0.mk))

structure Tests.Legacy__naming.Functions_defined_in_trait_impls.B where


def
  Tests.Legacy__naming.Functions_defined_in_trait_impls.Impl_1.eq.panic_cold_explicit
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Never
  := do
  (← Core.Panicking.panic_explicit Rust_primitives.Hax.Tuple0.mk)

instance Tests.Legacy__naming.Functions_defined_in_trait_impls.Impl_1 :
  Core.Cmp.PartialEq
  Tests.Legacy__naming.Functions_defined_in_trait_impls.B
  Tests.Legacy__naming.Functions_defined_in_trait_impls.B
  where
  eq (self : Tests.Legacy__naming.Functions_defined_in_trait_impls.B)
    (other : Tests.Legacy__naming.Functions_defined_in_trait_impls.B)
    := do
    (← Rust_primitives.Hax.never_to_any
        (← Tests.Legacy__naming.Functions_defined_in_trait_impls.Impl_1.eq.panic_cold_explicit
            Rust_primitives.Hax.Tuple0.mk))

--  @fail(extraction): ssprove(HAX0001)
def Tests.Legacy__naming.Ambiguous_names.debug
  (label : u32)
  (value : u32)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let args : (Rust_primitives.Hax.Tuple2 u32 u32) ← (pure
    (Rust_primitives.Hax.Tuple2.mk label value));
  let args : (RustArray Core.Fmt.Rt.Argument 2) ← (pure
    #v[(← Core.Fmt.Rt.Impl.new_display u32
             (Rust_primitives.Hax.Tuple0._0 args)),
         (← Core.Fmt.Rt.Impl.new_display u32
             (Rust_primitives.Hax.Tuple0._1 args))]);
  let _ ← (pure
    (← Std.Io.Stdio._print
        (← Core.Fmt.Rt.Impl_1.new_v1 (3 : usize) (2 : usize)
            #v["[", "] a=", "
"]
            args)));
  Rust_primitives.Hax.Tuple0.mk

--  `f` stacks mutliple let bindings declaring different `a`s.
def Tests.Legacy__naming.Ambiguous_names.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let a_1 : u32 ← (pure (104 : u32));
  let a_2 : u32 ← (pure (205 : u32));
  let a_3 : u32 ← (pure (306 : u32));
  let a : u32 ← (pure (123 : u32));
  let _ ← (pure (← Tests.Legacy__naming.Ambiguous_names.debug (3 : u32) a_3));
  let _ ← (pure (← Tests.Legacy__naming.Ambiguous_names.debug (2 : u32) a_2));
  let _ ← (pure (← Tests.Legacy__naming.Ambiguous_names.debug (1 : u32) a_1));
  (← Tests.Legacy__naming.Ambiguous_names.debug (4 : u32) a)

--  `f` is expanded into `f_expand` below, while the execution of `f` gives:
-- 
--  ```plaintext
--   [3] a=306
--   [2] a=205
--   [1] a=104
--   [last] a=123
--  ```
def Tests.Legacy__naming.Ambiguous_names.f_expand
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let a : i32 ← (pure (104 : i32));
  let a : i32 ← (pure (205 : i32));
  let a : i32 ← (pure (306 : i32));
  let a : u32 ← (pure (123 : u32));
  let _ ← (pure (← Tests.Legacy__naming.Ambiguous_names.debug (3 : u32) a));
  let _ ← (pure (← Tests.Legacy__naming.Ambiguous_names.debug (2 : u32) a));
  let _ ← (pure (← Tests.Legacy__naming.Ambiguous_names.debug (1 : u32) a));
  (← Tests.Legacy__naming.Ambiguous_names.debug (0 : u32) a)

inductive Tests.Legacy__naming.Foo : Type
| A : Tests.Legacy__naming.Foo 
| B (x : usize) : Tests.Legacy__naming.Foo 


inductive Tests.Legacy__naming.Foo2 : Type
| A : Tests.Legacy__naming.Foo2 
| B (x : usize) : Tests.Legacy__naming.Foo2 


structure Tests.Legacy__naming.B where


structure Tests.Legacy__naming.C where
  x : usize

structure Tests.Legacy__naming.X where


def Tests.Legacy__naming.mk_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Tests.Legacy__naming.C
  := do
  let _ ← (pure (Tests.Legacy__naming.Foo.B (x := (3 : usize))));
  let _ ← (pure Tests.Legacy__naming.X.mk);
  (Tests.Legacy__naming.C.mk (x := (3 : usize)))

def Tests.Legacy__naming.Impl.f
  (self : Tests.Legacy__naming.Foo)
  : Result Tests.Legacy__naming.Foo
  := do
  Tests.Legacy__naming.Foo.A

def Tests.Legacy__naming.Impl_1.f
  (self : Tests.Legacy__naming.B)
  : Result Tests.Legacy__naming.B
  := do
  Tests.Legacy__naming.B.mk

structure Tests.Legacy__naming.Foobar where
  a : Tests.Legacy__naming.Foo

def Tests.Legacy__naming.f.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__naming.f.g.Impl.g
  (self : Tests.Legacy__naming.B)
  : Result usize
  := do
  (0 : usize)

inductive Tests.Legacy__naming.f.g.Impl.g.Foo : Type
| A : Tests.Legacy__naming.f.g.Impl.g.Foo 
| B (x : usize) : Tests.Legacy__naming.f.g.Impl.g.Foo 


def Tests.Legacy__naming.f.g.Impl_1.g
  (self : Tests.Legacy__naming.Foo)
  : Result usize
  := do
  (1 : usize)

def Tests.Legacy__naming.f
  (x : Tests.Legacy__naming.Foobar)
  : Result usize
  := do
  (← Tests.Legacy__naming.f.g.Impl_1.g (Tests.Legacy__naming.Foobar.a x))

def Tests.Legacy__naming.f.g.Impl_1.g.Hello.h
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__naming.reserved_names
  (val : u8)
  (noeq : u8)
  (of : u8)
  : Result u8
  := do
  (← (← val +? noeq) +? of)

structure Tests.Legacy__naming.Arity1 (T : Type) where
  _0 : T

class Tests.Legacy__naming.T1 (Self : Type) where


instance Tests.Legacy__naming.Impl_2 :
  Tests.Legacy__naming.T1 Tests.Legacy__naming.Foo
  where


instance Tests.Legacy__naming.Impl_3 :
  Tests.Legacy__naming.T1
  (Rust_primitives.Hax.Tuple2 Tests.Legacy__naming.Foo u8)
  where


class Tests.Legacy__naming.T2_for_a (Self : Type) where


instance Tests.Legacy__naming.Impl_4 :
  Tests.Legacy__naming.T2_for_a
  (Tests.Legacy__naming.Arity1
    (Rust_primitives.Hax.Tuple2 Tests.Legacy__naming.Foo u8))
  where


class Tests.Legacy__naming.T3_e_for_a (Self : Type) where


instance Tests.Legacy__naming.Impl_5 :
  Tests.Legacy__naming.T3_e_for_a Tests.Legacy__naming.Foo
  where


structure Tests.Legacy__naming.StructA where
  a : usize

structure Tests.Legacy__naming.StructB where
  a : usize
  b : usize

structure Tests.Legacy__naming.StructC where
  a : usize

structure Tests.Legacy__naming.StructD where
  a : usize
  b : usize

def Tests.Legacy__naming.construct_structs
  (a : usize)
  (b : usize)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure (Tests.Legacy__naming.StructA.mk (a := a)));
  let _ ← (pure (Tests.Legacy__naming.StructB.mk (a := a) (b := b)));
  let _ ← (pure (Tests.Legacy__naming.StructC.mk (a := a)));
  let _ ← (pure (Tests.Legacy__naming.StructD.mk (a := a) (b := b)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__naming.INHERENT_CONSTANT : usize := 3

class Tests.Legacy__naming.FooTrait (Self : Type) where
  ASSOCIATED_CONSTANT : usize

def Tests.Legacy__naming.constants
  (T : Type) [(Tests.Legacy__naming.FooTrait T)] (_ :
  Rust_primitives.Hax.Tuple0)
  : Result usize
  := do
  (← (← Tests.Legacy__naming.FooTrait.ASSOCIATED_CONSTANT)
    +? Tests.Legacy__naming.INHERENT_CONSTANT)

--  From issue https://github.com/hacspec/hax/issues/839
def Tests.Legacy__naming.string_shadows
  (string : String)
  (n : String)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

--  From issue https://github.com/cryspen/hax/issues/1450
def Tests.Legacy__naming.items_under_closures
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (fun _ => (do
        Rust_primitives.Hax.Tuple0.mk : Result Rust_primitives.Hax.Tuple0)));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__naming.items_under_closures.Closure.nested_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__naming.items_under_closures.Closure.NestedStruct where


def Tests.Legacy__naming.items_under_closures.nested_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

structure Tests.Legacy__naming.items_under_closures.NestedStruct where
  