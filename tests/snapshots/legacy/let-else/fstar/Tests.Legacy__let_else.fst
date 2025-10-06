module Tests.Legacy__let_else
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let let_else (opt: Core.Option.t_Option u32) : bool =
  match opt <: Core.Option.t_Option u32 with
  | Core.Option.Option_Some x -> true
  | _ -> false

let let_else_different_type (opt: Core.Option.t_Option u32) : bool =
  match opt <: Core.Option.t_Option u32 with
  | Core.Option.Option_Some x ->
    let_else (Core.Option.Option_Some (x +! mk_u32 1 <: u32) <: Core.Option.t_Option u32)
  | _ -> false
