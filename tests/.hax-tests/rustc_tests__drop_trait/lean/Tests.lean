
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

structure Tests.Rustc_tests__drop_trait.Firework where
  strength : i32

instance Tests.Rustc_tests__drop_trait.Impl :
  Core.Ops.Drop.Drop Tests.Rustc_tests__drop_trait.Firework
  where
  drop (self : Tests.Rustc_tests__drop_trait.Firework) := do
    let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
      #v[(← Core.Fmt.Rt.Impl.new_display i32
               (Tests.Rustc_tests__drop_trait.Firework.strength self))]);
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
              #v["BOOM times ", "!!!
"]
              args)));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    self

def Tests.Rustc_tests__drop_trait.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
  := do
  let _firecracker : Tests.Rustc_tests__drop_trait.Firework ← (pure
    (Tests.Rustc_tests__drop_trait.Firework.mk (strength := (1 : i32))));
  let _tnt : Tests.Rustc_tests__drop_trait.Firework ← (pure
    (Tests.Rustc_tests__drop_trait.Firework.mk (strength := (100 : i32))));
  (← if true then do
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_const (1 : usize)
              #v["Exiting with error...
"])));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    (Core.Result.Result.Err (1 : u8))
  else do
    let _ ← (pure
      (Tests.Rustc_tests__drop_trait.Firework.mk (strength := (1000 : i32))));
    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk))