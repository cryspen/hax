module Tests.Legacy__lean_tests__lib.Loops.Errors
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Error =
  | Error_Foo : t_Error
  | Error_Bar : u32 -> t_Error

/// @fail(extraction): proverif(HAX0008)
let loop3 (_: Prims.unit) : Core.Result.t_Result u32 t_Error =
  let x:u32 = mk_u32 0 in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_i32 1)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:u32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x i ->
          let x:u32 = x in
          let i:i32 = i in
          if i =. mk_i32 5 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break
              (Core.Result.Result_Err (Error_Foo <: t_Error) <: Core.Result.t_Result u32 t_Error)
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result u32 t_Error)
                (Prims.unit & u32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result u32 t_Error)
                  (Prims.unit & u32)) u32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (x +! mk_u32 5 <: u32)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result u32 t_Error)
                  (Prims.unit & u32)) u32)
    <:
    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result u32 t_Error) u32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue x ->
    Core.Result.Result_Ok x <: Core.Result.t_Result u32 t_Error

/// @fail(extraction): proverif(HAX0008)
let loop4 (_: Prims.unit) : Core.Result.t_Result (u32 & u32) t_Error =
  let e:u32 = mk_u32 0 in
  let f: Prims.unit -> u32 =
    fun temp_0_ ->
      let ():Prims.unit = temp_0_ in
      mk_u32 42
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_u32 0)
      (Core.Ops.Function.f_call #Prims.unit
          #FStar.Tactics.Typeclasses.solve
          f
          ((() <: Prims.unit) <: Prims.unit)
        <:
        u32)
      (fun e temp_1_ ->
          let e:u32 = e in
          let _:u32 = temp_1_ in
          true)
      e
      (fun e i ->
          let e:u32 = e in
          let i:u32 = i in
          if i >. mk_u32 10 <: bool
          then
            Core.Ops.Control_flow.ControlFlow_Break
            (Core.Ops.Control_flow.ControlFlow_Break
              (Core.Result.Result_Err (Error_Bar e <: t_Error)
                <:
                Core.Result.t_Result (u32 & u32) t_Error)
              <:
              Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (u32 & u32) t_Error)
                (Prims.unit & u32))
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (u32 & u32) t_Error)
                  (Prims.unit & u32)) u32
          else
            Core.Ops.Control_flow.ControlFlow_Continue (e +! i <: u32)
            <:
            Core.Ops.Control_flow.t_ControlFlow
              (Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (u32 & u32) t_Error)
                  (Prims.unit & u32)) u32)
    <:
    Core.Ops.Control_flow.t_ControlFlow (Core.Result.t_Result (u32 & u32) t_Error) u32
  with
  | Core.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core.Ops.Control_flow.ControlFlow_Continue e ->
    Core.Result.Result_Ok (e, e <: (u32 & u32)) <: Core.Result.t_Result (u32 & u32) t_Error
