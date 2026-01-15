
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

def Tests.Legacy__reordering.Mut_rec.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Mut_rec.f Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.Mut_rec.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Mut_rec.g Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.Mut_rec.f_2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Mut_rec.f Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.Independent_cycles.c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Independent_cycles.a Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.Independent_cycles.a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Independent_cycles.c Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.Independent_cycles.d
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Independent_cycles.b Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.Independent_cycles.b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (Tests.Legacy__reordering.Independent_cycles.d Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.no_dependency_1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (pure Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__reordering.no_dependency_2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (pure Rust_primitives.Hax.Tuple0.mk)

inductive Tests.Legacy__reordering.Foo : Type
| A : Tests.Legacy__reordering.Foo
| B : Tests.Legacy__reordering.Foo


def Tests.Legacy__reordering.f
  (_ : u32)
  : Result Tests.Legacy__reordering.Foo
  := do
  (pure Tests.Legacy__reordering.Foo.A)

structure Tests.Legacy__reordering.Bar where
  _0 : Tests.Legacy__reordering.Foo

def Tests.Legacy__reordering.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Tests.Legacy__reordering.Bar
  := do
  (pure (Tests.Legacy__reordering.Bar.mk
    (← (Tests.Legacy__reordering.f (32 : u32)))))

def Tests.Legacy__reordering.Foo
  (x : Tests.Legacy__reordering.Foo)
  : Result isize
  := do
  match x with
    | (Tests.Legacy__reordering.Foo.A ) => (pure (0 : isize))
    | (Tests.Legacy__reordering.Foo.B ) => (pure (1 : isize))