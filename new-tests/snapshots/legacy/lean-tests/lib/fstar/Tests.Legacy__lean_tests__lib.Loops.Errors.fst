module Tests.Legacy__lean_tests__lib.Loops.Errors
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Error =
  | Error_Foo : t_Error
  | Error_Bar : u32 -> t_Error

/// @fail(extraction): proverif(HAX0008)
let loop3 (_: Prims.unit) : Core_models.Result.t_Result u32 t_Error =
  let x:u32 = mk_u32 0 in
  let (v_end: u32):u32 = mk_u32 10 in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_u32 1)
      v_end
      (fun x temp_1_ ->
          let x:u32 = x in
          let _:u32 = temp_1_ in
          true)
      x
      (fun x i ->
          let x:u32 = x in
          let i:u32 = i in
          if i =. mk_u32 5 <: bool
          then
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err (Error_Foo <: t_Error)
                <:
                Core_models.Result.t_Result u32 t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result u32 t_Error)
                (Prims.unit & u32))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result u32 t_Error)
                  (Prims.unit & u32)) u32
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue (x +! mk_u32 5 <: u32)
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result u32 t_Error)
                  (Prims.unit & u32)) u32)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result u32 t_Error) u32
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue x ->
    Core_models.Result.Result_Ok x <: Core_models.Result.t_Result u32 t_Error

/// @fail(extraction): proverif(HAX0008)
let loop4 (_: Prims.unit) : Core_models.Result.t_Result (u32 & u32) t_Error =
  let e:u32 = mk_u32 0 in
  let f: Prims.unit -> u32 =
    fun temp_0_ ->
      let ():Prims.unit = temp_0_ in
      mk_u32 42
  in
  match
    Rust_primitives.Hax.Folds.fold_range_return (mk_u32 0)
      (Core_models.Ops.Function.f_call #Prims.unit
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
            Core_models.Ops.Control_flow.ControlFlow_Break
            (Core_models.Ops.Control_flow.ControlFlow_Break
              (Core_models.Result.Result_Err (Error_Bar e <: t_Error)
                <:
                Core_models.Result.t_Result (u32 & u32) t_Error)
              <:
              Core_models.Ops.Control_flow.t_ControlFlow
                (Core_models.Result.t_Result (u32 & u32) t_Error) (Prims.unit & u32))
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (u32 & u32) t_Error) (Prims.unit & u32)) u32
          else
            Core_models.Ops.Control_flow.ControlFlow_Continue (e +! i <: u32)
            <:
            Core_models.Ops.Control_flow.t_ControlFlow
              (Core_models.Ops.Control_flow.t_ControlFlow
                  (Core_models.Result.t_Result (u32 & u32) t_Error) (Prims.unit & u32)) u32)
    <:
    Core_models.Ops.Control_flow.t_ControlFlow (Core_models.Result.t_Result (u32 & u32) t_Error) u32
  with
  | Core_models.Ops.Control_flow.ControlFlow_Break ret -> ret
  | Core_models.Ops.Control_flow.ControlFlow_Continue e ->
    Core_models.Result.Result_Ok (e, e <: (u32 & u32))
    <:
    Core_models.Result.t_Result (u32 & u32) t_Error
