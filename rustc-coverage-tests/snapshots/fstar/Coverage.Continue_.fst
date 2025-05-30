module Coverage.Continue_
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
  let x:i32 = mk_i32 0 in
  let x:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          match is_true <: bool with
          | true -> x
          | _ ->
            let x:i32 = mk_i32 1 in
            mk_i32 3)
  in
  let x:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          match is_true <: bool with
          | false ->
            let x:i32 = mk_i32 1 in
            mk_i32 3
          | _ -> x)
  in
  let x:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          match is_true <: bool with
          | true ->
            let x:i32 = mk_i32 1 in
            mk_i32 3
          | _ -> x)
  in
  let x:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          if is_true then x else mk_i32 3)
  in
  let x:i32 =
    Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          let x:i32 =
            match is_true <: bool with
            | false ->
              let x:i32 = mk_i32 1 in
              x
            | _ ->
              let _:i32 = x in
              x
          in
          let x:i32 = mk_i32 3 in
          x)
  in
  let x:i32 =
    Rust_primitives.Hax.Folds.fold_range_cf (mk_i32 0)
      (mk_i32 10)
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          true)
      x
      (fun x temp_1_ ->
          let x:i32 = x in
          let _:i32 = temp_1_ in
          match is_true <: bool with
          | false ->
            let x:i32 = mk_i32 1 in
            Core.Ops.Control_flow.ControlFlow_Continue (mk_i32 3)
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32
          | _ ->
            Core.Ops.Control_flow.ControlFlow_Break ((), x <: (Prims.unit & i32))
            <:
            Core.Ops.Control_flow.t_ControlFlow (Prims.unit & i32) i32)
  in
  let _:i32 = x in
  ()
