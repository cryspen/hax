module Coverage.Fn_sig_into_try
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let a (_: Prims.unit) : Core.Option.t_Option i32 =
  let _:Core.Option.t_Option i32 = Core.Option.Option_Some (mk_i32 7) <: Core.Option.t_Option i32 in
  Core.Option.Option_Some (mk_i32 0) <: Core.Option.t_Option i32

let b (_: Prims.unit) : Core.Option.t_Option i32 =
  match Core.Option.Option_Some (mk_i32 7) <: Core.Option.t_Option i32 with
  | Core.Option.Option_Some _ -> Core.Option.Option_Some (mk_i32 0) <: Core.Option.t_Option i32
  | Core.Option.Option_None  -> Core.Option.Option_None <: Core.Option.t_Option i32

let c (_: Prims.unit) : Core.Option.t_Option i32 =
  match Core.Option.Option_Some (mk_i32 7) <: Core.Option.t_Option i32 with
  | Core.Option.Option_Some _ -> Core.Option.Option_Some (mk_i32 0) <: Core.Option.t_Option i32
  | Core.Option.Option_None  -> Core.Option.Option_None <: Core.Option.t_Option i32

let d (_: Prims.unit) : Core.Option.t_Option i32 =
  let _:Prims.unit = () <: Prims.unit in
  match Core.Option.Option_Some (mk_i32 7) <: Core.Option.t_Option i32 with
  | Core.Option.Option_Some _ -> Core.Option.Option_Some (mk_i32 0) <: Core.Option.t_Option i32
  | Core.Option.Option_None  -> Core.Option.Option_None <: Core.Option.t_Option i32

let main (_: Prims.unit) : Prims.unit =
  let _:Core.Option.t_Option i32 = a () in
  let _:Core.Option.t_Option i32 = b () in
  let _:Core.Option.t_Option i32 = c () in
  let _:Core.Option.t_Option i32 = d () in
  ()
