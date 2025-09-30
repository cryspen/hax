
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

def Tests.Rustc_tests__while_early_ret.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
  := do
  let countdown : i32 ← (pure (10 : i32));
  (match
    (← Rust_primitives.Hax.while_loop_return
        (fun countdown => (do
            (← Rust_primitives.Hax.Machine_int.gt countdown (0 : i32)) : Result
            Bool))
        (fun countdown => (do true : Result Bool))
        (fun countdown => (do
            (← Rust_primitives.Hax.Int.from_machine (0 : u32)) : Result
            Hax_lib.Int.Int))
        countdown
        (fun countdown => (do
            (← if
            (← Rust_primitives.Hax.Machine_int.lt countdown (5 : i32)) then do
              (Core.Ops.Control_flow.ControlFlow.Break
                (Core.Ops.Control_flow.ControlFlow.Break
                  (← if
                  (← Rust_primitives.Hax.Machine_int.gt countdown (8 : i32))
                  then do
                    (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk)
                  else do
                    (Core.Result.Result.Err (1 : u8)))))
            else do
              (Core.Ops.Control_flow.ControlFlow.Continue
                (← countdown -? (1 : i32)))) : Result
            (Core.Ops.Control_flow.ControlFlow
              (Core.Ops.Control_flow.ControlFlow
                (Core.Result.Result Rust_primitives.Hax.Tuple0 u8)
                (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 i32))
              i32))))
  with
    | (Core.Ops.Control_flow.ControlFlow.Break ret) => do ret
    | (Core.Ops.Control_flow.ControlFlow.Continue countdown)
      => do (Core.Result.Result.Ok Rust_primitives.Hax.Tuple0.mk))