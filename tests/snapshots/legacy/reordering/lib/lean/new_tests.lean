
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


namespace new_tests.legacy__reordering__lib

def no_dependency_1 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def no_dependency_2 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

inductive Foo : Type
| A : Foo
| B : Foo

def f (_ : u32) : RustM Foo := do (pure Foo.A)

structure Bar where
  _0 : Foo

def g (_ : rust_primitives.hax.Tuple0) : RustM Bar := do
  (pure (Bar.mk (← (f (32 : u32)))))

def Foo_cast_to_repr (x : Foo) : RustM isize := do
  match x with | (Foo.A ) => (pure (0 : isize)) | (Foo.B ) => (pure (1 : isize))

end new_tests.legacy__reordering__lib


namespace new_tests.legacy__reordering__lib.mut_rec

def g (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (f rust_primitives.hax.Tuple0.mk)

def f (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (g rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__reordering__lib.mut_rec


namespace new_tests.legacy__reordering__lib.independent_cycles

def c (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (a rust_primitives.hax.Tuple0.mk)

def a (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (c rust_primitives.hax.Tuple0.mk)

def d (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (b rust_primitives.hax.Tuple0.mk)

def b (_ : rust_primitives.hax.Tuple0) : RustM rust_primitives.hax.Tuple0 := do
  (d rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__reordering__lib.independent_cycles


namespace new_tests.legacy__reordering__lib.mut_rec

def f_2 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (f rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__reordering__lib.mut_rec

