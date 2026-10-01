
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__generics

structure Firework
  (T : Type)
  [trait_constr_Firework_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Firework_i0 : core_models.marker.Copy T ]
  [trait_constr_Firework_associated_type_i1 :
    core_models.fmt.Display.AssociatedTypes
    T]
  [trait_constr_Firework_i1 : core_models.fmt.Display T ]
  where
  strength : T

@[spec]
def Impl.set_strength
    (T : Type)
    [trait_constr_set_strength_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_set_strength_i0 : core_models.marker.Copy T ]
    [trait_constr_set_strength_associated_type_i1 :
      core_models.fmt.Display.AssociatedTypes
      T]
    [trait_constr_set_strength_i1 : core_models.fmt.Display T ]
    (self : (Firework T))
    (new_strength : T) :
    RustM (Firework T) := do
  let self : (Firework T) := {self with strength := new_strength};
  (pure self)

@[spec]
def Impl_1.drop_hoisted
    (T : Type)
    [trait_constr_drop_hoisted_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_drop_hoisted_i0 : core_models.marker.Copy T ]
    [trait_constr_drop_hoisted_associated_type_i1 :
      core_models.fmt.Display.AssociatedTypes
      T]
    [trait_constr_drop_hoisted_i1 : core_models.fmt.Display T ]
    (self : (Firework T)) :
    RustM (Firework T) := do
  let args : (rust_primitives.hax.Tuple1 T) :=
    (rust_primitives.hax.Tuple1.mk (Firework.strength self));
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display T
                            (rust_primitives.hax.Tuple1._0 args)))]);
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        (RustArray.ofVec #v["BOOM times ", "!!!\n"])
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure self)

--  @fail(extraction): ssprove(HAX0001)
@[reducible] instance Impl_1.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : core_models.marker.Copy T ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.fmt.Display.AssociatedTypes
    T]
  [trait_constr_Impl_1_i1 : core_models.fmt.Display T ] :
  core_models.ops.drop.Drop.AssociatedTypes (Firework T)
  where

instance Impl_1
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.marker.Copy.AssociatedTypes
    T]
  [trait_constr_Impl_1_i0 : core_models.marker.Copy T ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.fmt.Display.AssociatedTypes
    T]
  [trait_constr_Impl_1_i1 : core_models.fmt.Display T ] :
  core_models.ops.drop.Drop (Firework T)
  where
  drop := (Impl_1.drop_hoisted T)

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.result.Result rust_primitives.hax.Tuple0 u8) := do
  let firecracker : (Firework i32) := (Firework.mk (strength := (1 : i32)));
  let firecracker : (Firework i32) ←
    (Impl.set_strength i32 firecracker (2 : i32));
  let tnt : (Firework f64) := (Firework.mk (strength := (100.1 : f64)));
  let tnt : (Firework f64) ← (Impl.set_strength f64 tnt (200.1 : f64));
  let tnt : (Firework f64) ← (Impl.set_strength f64 tnt (300.3 : f64));
  if true then do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["Exiting with error...\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure (core_models.result.Result.Err (1 : u8)))
  else do
    let _ := (Firework.mk (strength := (1000 : i32)));
    (pure (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk))

end new_tests.rustc_coverage__generics

