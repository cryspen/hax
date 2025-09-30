
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

structure Tests.Rustc_tests__generics.Firework
  (T : Type) [(Core.Marker.Copy T)] [(Core.Fmt.Display T)] where
  strength : T

def Tests.Rustc_tests__generics.Impl.set_strength
  (T : Type) [(Core.Marker.Copy T)] [(Core.Fmt.Display T)] (self :
  (Tests.Rustc_tests__generics.Firework T))
  (new_strength : T)
  : Result (Tests.Rustc_tests__generics.Firework T)
  := do
  let self : (Tests.Rustc_tests__generics.Firework T) ← (pure
    -- Unsupported base expressions for structs.);
  self

instance Tests.Rustc_tests__generics.Impl_1
  (T : Type) [(Core.Marker.Copy T)] [(Core.Fmt.Display T)] :
  Core.Ops.Drop.Drop (Tests.Rustc_tests__generics.Firework T)
  where
  drop (self : (Tests.Rustc_tests__generics.Firework T)) := do
    let args : (RustArray Core.Fmt.Rt.Argument (1 : usize)) ← (pure
      #v[(← Core.Fmt.Rt.Impl.new_display T
               (Tests.Rustc_tests__generics.Firework.strength self))]);
    let _ ← (pure
      (← Std.Io.Stdio._print
          (← Core.Fmt.Rt.Impl_1.new_v1 (2 : usize) (1 : usize)
              #v["BOOM times ", "!!!
"]
              args)));
    let _ ← (pure Rust_primitives.Hax.Tuple0.mk);
    self

def Tests.Rustc_tests__generics.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
  := do
  let firecracker : (Tests.Rustc_tests__generics.Firework i32) ← (pure
    (Tests.Rustc_tests__generics.Firework.mk (strength := (1 : i32))));
  let firecracker : (Tests.Rustc_tests__generics.Firework i32) ← (pure
    (← Tests.Rustc_tests__generics.Impl.set_strength i32
        firecracker
        (2 : i32)));
  let tnt : (Tests.Rustc_tests__generics.Firework TODO_LINE_739) ← (pure
    (Tests.Rustc_tests__generics.Firework.mk (strength := TODO_LINE_722)));
  let tnt : (Tests.Rustc_tests__generics.Firework TODO_LINE_739) ← (pure
    (← Tests.Rustc_tests__generics.Impl.set_strength TODO_LINE_739
        tnt
        TODO_LINE_722));
  let tnt : (Tests.Rustc_tests__generics.Firework TODO_LINE_739) ← (pure
    (← Tests.Rustc_tests__generics.Impl.set_strength TODO_LINE_739
        tnt
        TODO_LINE_722));
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
      (Tests.Rustc_tests__generics.Firework.mk (strength := (1000 : i32))));
    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk))