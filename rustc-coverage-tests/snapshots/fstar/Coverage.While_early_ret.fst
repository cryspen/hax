module Coverage.While_early_ret
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  let countdown:i32 = mk_i32 10 in
  match
    Rust_primitives.Hax.while_loop_return (fun countdown ->
          let countdown:i32 = countdown in
          countdown >. mk_i32 0 <: bool)
      (fun countdown ->
          let countdown:i32 = countdown in
          true)
      (fun countdown ->
          let countdown:i32 = countdown in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      countdown
      (fun countdown ->
          let countdown:i32 = countdown in
          if countdown <. mk_i32 5 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break
              (if countdown >. mk_i32 8 <: bool
                then Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
                else Core.Result.Result_Err (mk_u8 1) <: Core.Result.t_Result Prims.unit u8)
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                  (Prims.unit & i32)) i32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (countdown -! mk_i32 1 <: i32)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8)
                  (Prims.unit & i32)) i32)
    <:
    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result Prims.unit u8) i32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue countdown ->
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
