
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

def Tests.Legacy__reordering__src__lib.Mut_rec.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Mut_rec.f Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.Mut_rec.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Mut_rec.g Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.Mut_rec.f_2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Mut_rec.f Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.Independent_cycles.c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Independent_cycles.a
      Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.Independent_cycles.a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Independent_cycles.c
      Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.Independent_cycles.d
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Independent_cycles.b
      Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.Independent_cycles.b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__reordering__src__lib.Independent_cycles.d
      Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering__src__lib.no_dependency_1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__reordering__src__lib.no_dependency_2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

inductive Tests.Legacy__reordering__src__lib.Foo : Type
| A : Tests.Legacy__reordering__src__lib.Foo 
| B : Tests.Legacy__reordering__src__lib.Foo 


def Tests.Legacy__reordering__src__lib.f
  (_ : u32)
  : Result Tests.Legacy__reordering__src__lib.Foo
  := do
  Tests.Legacy__reordering__src__lib.Foo.A

structure Tests.Legacy__reordering__src__lib.Bar where
  _0 : Tests.Legacy__reordering__src__lib.Foo

def Tests.Legacy__reordering__src__lib.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Tests.Legacy__reordering__src__lib.Bar
  := do
  (Tests.Legacy__reordering__src__lib.Bar.mk
    (← Tests.Legacy__reordering__src__lib.f (32 : u32)))

def Tests.Legacy__reordering__src__lib.Foo
  (x : Tests.Legacy__reordering__src__lib.Foo)
  : Result isize
  := do
  (match x with
    | (Tests.Legacy__reordering__src__lib.Foo.A ) => do (0 : isize)
    | (Tests.Legacy__reordering__src__lib.Foo.B ) => do (1 : isize))