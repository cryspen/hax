module Coverage.Lazy_boolean
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
  let a, b, c:(i32 & i32 & i32) = mk_i32 0, mk_i32 0, mk_i32 0 <: (i32 & i32 & i32) in
  let a, b, c:(i32 & i32 & i32) =
    if is_true
    then
      let a:i32 = mk_i32 1 in
      let b:i32 = mk_i32 10 in
      let c:i32 = mk_i32 100 in
      a, b, c <: (i32 & i32 & i32)
    else a, b, c <: (i32 & i32 & i32)
  in
  let somebool:bool = a <. b || b <. c in
  let somebool:bool = b <. a || b <. c in
  let somebool:bool = a <. b && b <. c in
  let somebool:bool = b <. a && b <. c in
  let a:i32 =
    if ~.is_true
    then
      let a:i32 = mk_i32 2 in
      a
    else a
  in
  let b, c:(i32 & i32) =
    if is_true
    then
      let b:i32 = mk_i32 30 in
      b, c <: (i32 & i32)
    else
      let c:i32 = mk_i32 400 in
      b, c <: (i32 & i32)
  in
  let a:i32 =
    if ~.is_true
    then
      let a:i32 = mk_i32 2 in
      a
    else a
  in
  if is_true
  then
    let b:i32 = mk_i32 30 in
    ()
  else
    let c:i32 = mk_i32 400 in
    ()
