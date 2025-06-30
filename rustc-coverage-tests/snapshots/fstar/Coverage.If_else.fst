module Coverage.If_else
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

let main (_: Prims.unit) : Prims.unit =
  let is_true:bool =
    (Core.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let countdown:i32 = mk_i32 0 in
  let countdown:i32 =
    if is_true
    then
      let countdown:i32 = mk_i32 10 in
      countdown
    else mk_i32 100
  in
  if is_true
  then
    let countdown:i32 = mk_i32 10 in
    ()
  else
    let countdown:i32 = mk_i32 100 in
    ()
