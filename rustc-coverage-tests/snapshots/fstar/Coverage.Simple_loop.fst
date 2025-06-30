module Coverage.Simple_loop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

let main (_: Prims.unit) : (i32 & Prims.unit) =
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
    else countdown
  in
  Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/933.\nPlease upvote or comment this issue if you see this error message.\nUnhandled loop kind"
    "{\n (loop {\n |countdown| {\n (if rust_primitives::hax::machine_int::eq(countdown, 0) {\n core::ops::control_flow::ControlFlow_Break(Tuple2(Tuple0, countdown))\n } else {\n core::ops::control_flow::ControlF..."
  ,
  ()
  <:
  (i32 & Prims.unit)
