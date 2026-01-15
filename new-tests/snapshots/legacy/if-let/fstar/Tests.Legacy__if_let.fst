module Tests.Legacy__if_let
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let fun_with_if_let (_: Prims.unit) : u8 =
  let x:Core_models.Option.t_Option u8 =
    Core_models.Option.Option_Some (mk_u8 5) <: Core_models.Option.t_Option u8
  in
  match x <: Core_models.Option.t_Option u8 with
  | Core_models.Option.Option_Some x -> x
  | _ -> mk_u8 7
