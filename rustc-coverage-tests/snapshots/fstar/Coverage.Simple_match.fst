module Coverage.Simple_match
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let is_true:bool =
    (Core_models.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let countdown:i32 = mk_i32 1 in
  let countdown:i32 =
    if is_true
    then
      let countdown:i32 = mk_i32 0 in
      countdown
    else countdown
  in
  Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
    "{\n for _ in (core_models::iter::traits::collect::f_into_iter(core_models::ops::range::Range {\n f_start: 0,\n f_end: 2,\n })) {\n rust_primitives::hax::failure(\n \"(AST import) something is not implemented..."
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
