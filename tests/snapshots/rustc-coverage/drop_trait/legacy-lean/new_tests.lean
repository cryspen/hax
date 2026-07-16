
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


namespace new_tests.rustc_coverage__drop_trait

structure Firework where
  strength : i32

@[spec]
def Impl.drop_hoisted (self : Firework) : RustM Firework := do
  let args : (rust_primitives.hax.Tuple1 i32) :=
    (rust_primitives.hax.Tuple1.mk (Firework.strength self));
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_display i32
                            (rust_primitives.hax.Tuple1._0 args)))]);
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        (RustArray.ofVec #v["BOOM times ", "!!!\n"])
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure self)

--  @fail(extraction): ssprove(HAX0001)
@[reducible] instance Impl.AssociatedTypes :
  core_models.ops.drop.Drop.AssociatedTypes Firework
  where

instance Impl : core_models.ops.drop.Drop Firework where
  drop := (Impl.drop_hoisted)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM (core_models.result.Result rust_primitives.hax.Tuple0 u8) := do
  let _firecracker : Firework := (Firework.mk (strength := (1 : i32)));
  let _tnt : Firework := (Firework.mk (strength := (100 : i32)));
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

end new_tests.rustc_coverage__drop_trait
