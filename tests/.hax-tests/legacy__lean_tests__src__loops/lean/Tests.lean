
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

inductive Tests.Legacy__lean_tests__src__loops.Errors.Error : Type
| Foo : Tests.Legacy__lean_tests__src__loops.Errors.Error 
| Bar : u32 -> Tests.Legacy__lean_tests__src__loops.Errors.Error 


def Tests.Legacy__lean_tests__src__loops.Errors.loop3
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result u32 Tests.Legacy__lean_tests__src__loops.Errors.Error)
  := do
  let x : u32 ← (pure (0 : u32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (1 : i32)
        (10 : i32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do
            (← if (← Rust_primitives.Hax.Machine_int.eq i (5 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break
                  (Core.Result.Result.Err
                    Tests.Legacy__lean_tests__src__loops.Errors.Error.Foo)))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← x +? (5 : u32)))) :
            Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result
                  u32
                  Tests.Legacy__lean_tests__src__loops.Errors.Error)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 u32))
              u32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue x)
      => do (Core.Result.Result.Ok x))

def Tests.Legacy__lean_tests__src__loops.Errors.loop4
  (_ : Rust_primitives.Hax.Tuple0)
  : Result
  (Core.Result.Result
    (Rust_primitives.Hax.Tuple2 u32 u32)
    Tests.Legacy__lean_tests__src__loops.Errors.Error)
  := do
  let e : u32 ← (pure (0 : u32));
  let f : Rust_primitives.Hax.Tuple0 -> Result u32 ← (pure
    (fun ⟨⟩ => (do (42 : u32) : Result u32)));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (0 : u32)
        (← Core.Ops.Function.Fn.call
            f
            (Rust_primitives.Hax.Tuple1.mk Rust_primitives.Hax.Tuple0.mk))
        (fun e _ => (do true : Result Bool))
        e
        (fun e i => (do
            (← if (← Rust_primitives.Hax.Machine_int.gt i (10 : u32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break
                  (Core.Result.Result.Err
                    (Tests.Legacy__lean_tests__src__loops.Errors.Error.Bar e))))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← e +? i))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result
                  (Rust_primitives.Hax.Tuple2 u32 u32)
                  Tests.Legacy__lean_tests__src__loops.Errors.Error)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 u32))
              u32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue e)
      => do (Core.Result.Result.Ok (Rust_primitives.Hax.Tuple2.mk e e)))

def Tests.Legacy__lean_tests__src__loops.loop1
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  let x ← (pure (0 : u32));
  let x : u32 ← (pure
    (← Rust_primitives.Hax.Folds.fold_range
        (1 : u32)
        (10 : u32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do (← x +? i) : Result u32))));
  x

def Tests.Legacy__lean_tests__src__loops.loop2
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u32
  := do
  let x ← (pure (0 : u32));
  (match
    (← Rust_primitives.Hax.Folds.fold_range_return
        (1 : u32)
        (10 : u32)
        (fun x _ => (do true : Result Bool))
        x
        (fun x i => (do
            (← if (← Rust_primitives.Hax.Machine_int.eq i (5 : u32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break x))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue (← x +? i))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                u32
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 u32))
              u32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue x) => do x)