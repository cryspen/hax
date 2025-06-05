module Coverage.Sort_groups
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

let generic_fn (#v_T: Type0) (cond: bool) : Prims.unit =
  if cond
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
            (mk_usize 1)
            (let list = [""; "\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
            (let list =
                [
                  Core.Fmt.Rt.impl__new_display #string (Core.Any.type_name #v_T () <: string)
                  <:
                  Core.Fmt.Rt.t_Argument
                ]
              in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let other_fn (_: Prims.unit) : Prims.unit = ()

let main (_: Prims.unit) : Prims.unit =
  let cond:bool =
    (Core.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) >.
    mk_usize 1
  in
  let _:Prims.unit = generic_fn #Prims.unit cond in
  let _:Prims.unit = generic_fn #string (~.cond <: bool) in
  let _:Prims.unit =
    if Core.Hint.black_box #bool false
    then
      let _:Prims.unit = generic_fn #char cond in
      ()
  in
  let _:Prims.unit = generic_fn #i32 cond in
  let _:Prims.unit = other_fn () in
  ()
