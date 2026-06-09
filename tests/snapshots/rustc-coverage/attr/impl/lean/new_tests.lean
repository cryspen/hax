
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


namespace new_tests.rustc_coverage__attr__impl

structure MyStruct where
  -- no fields

@[spec]
def Impl.off_inherit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl.off_on (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl.off_off (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl_1.on_inherit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl_1.on_on (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl_1.on_off (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

class MyTrait.AssociatedTypes (Self : Type) where

class MyTrait (Self : Type)
  [associatedTypes : outParam (MyTrait.AssociatedTypes (Self : Type))]
  where
  method (Self) :
    (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)

@[spec]
def Impl_2.method_hoisted (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[reducible] instance Impl_2.AssociatedTypes :
  MyTrait.AssociatedTypes MyStruct
  where

instance Impl_2 : MyTrait MyStruct where
  method := (Impl_2.method_hoisted)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__attr__impl

