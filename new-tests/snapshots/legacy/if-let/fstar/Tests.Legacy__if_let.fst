module Tests.Legacy__if_let
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let fun_with_if_let (_: Prims.unit) : u8 =
  let x:Core.Option.t_Option u8 = Core.Option.Option_Some (mk_u8 5) <: Core.Option.t_Option u8 in
  match x <: Core.Option.t_Option u8 with
  | Core.Option.Option_Some x -> x
  | _ -> mk_u8 7
