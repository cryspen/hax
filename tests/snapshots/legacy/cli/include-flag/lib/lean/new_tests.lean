
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


namespace new_tests.legacy__cli__include_flag__lib

structure Foo where
  -- no fields

class Trait.AssociatedTypes (Self : Type) where

class Trait (Self : Type)
  [associatedTypes : outParam (Trait.AssociatedTypes (Self : Type))]
  where

@[reducible] instance Impl.AssociatedTypes : Trait.AssociatedTypes Foo where

instance Impl : Trait Foo where

--  Indirect dependencies
def main_a_a (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_b_a (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_c_a (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_a_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_b_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_c_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_a_c (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

--  Direct dependencies
def main_a
    (T : Type)
    [trait_constr_main_a_associated_type_i0 : Trait.AssociatedTypes T]
    [trait_constr_main_a_i0 : Trait T ]
    (x : T) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (main_a_a rust_primitives.hax.Tuple0.mk);
  let _ ← (main_a_b rust_primitives.hax.Tuple0.mk);
  let _ ← (main_a_c rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

def main_b_c (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (main_b_a rust_primitives.hax.Tuple0.mk);
  let _ ← (main_b_b rust_primitives.hax.Tuple0.mk);
  let _ ← (main_b_c rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

def main_c_c (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

def main_c (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (main_c_a rust_primitives.hax.Tuple0.mk);
  let _ ← (main_c_b rust_primitives.hax.Tuple0.mk);
  let _ ← (main_c_c rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

--  Entrypoint
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (main_a Foo Foo.mk);
  let _ ← (main_b rust_primitives.hax.Tuple0.mk);
  let _ ← (main_c rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__cli__include_flag__lib

