module Tests.Legacy__side_effects.Nested_return
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let other_fun (rng: i8) : (i8 & Core_models.Result.t_Result Prims.unit Prims.unit) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Prims.unit =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Prims.unit
  in
  rng, hax_temp_output <: (i8 & Core_models.Result.t_Result Prims.unit Prims.unit)

let v_fun (rng: i8) : (i8 & Core_models.Result.t_Result Prims.unit Prims.unit) =
  let (tmp0: i8), (out: Core_models.Result.t_Result Prims.unit Prims.unit) = other_fun rng in
  let rng:i8 = tmp0 in
  match out <: Core_models.Result.t_Result Prims.unit Prims.unit with
  | Core_models.Result.Result_Ok hoist41 ->
    rng, (Core_models.Result.Result_Ok hoist41 <: Core_models.Result.t_Result Prims.unit Prims.unit)
    <:
    (i8 & Core_models.Result.t_Result Prims.unit Prims.unit)
  | Core_models.Result.Result_Err err ->
    rng, (Core_models.Result.Result_Err err <: Core_models.Result.t_Result Prims.unit Prims.unit)
    <:
    (i8 & Core_models.Result.t_Result Prims.unit Prims.unit)
