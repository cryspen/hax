module Tests.Legacy__side_effects.Nested_return
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let other_fun (rng: i8) : (i8 & Core.Result.t_Result Prims.unit Prims.unit) =
  let hax_temp_output:Core.Result.t_Result Prims.unit Prims.unit =
    Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit Prims.unit
  in
  rng, hax_temp_output <: (i8 & Core.Result.t_Result Prims.unit Prims.unit)

let v_fun (rng: i8) : (i8 & Core.Result.t_Result Prims.unit Prims.unit) =
  let tmp0, out:(i8 & Core.Result.t_Result Prims.unit Prims.unit) = other_fun rng in
  let rng:i8 = tmp0 in
  match out <: Core.Result.t_Result Prims.unit Prims.unit with
  | Core.Result.Result_Ok hoist41 ->
    rng, (Core.Result.Result_Ok hoist41 <: Core.Result.t_Result Prims.unit Prims.unit)
    <:
    (i8 & Core.Result.t_Result Prims.unit Prims.unit)
  | Core.Result.Result_Err err ->
    rng, (Core.Result.Result_Err err <: Core.Result.t_Result Prims.unit Prims.unit)
    <:
    (i8 & Core.Result.t_Result Prims.unit Prims.unit)
