module Coverage.Auxiliary.Used_inline_crate
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Std.Env in
  ()

let used_only_from_bin_crate_generic_function
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T)
      (arg: v_T)
    : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = ["used_only_from_bin_crate_generic_function with "; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #v_T arg <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()

let used_only_from_this_lib_crate_generic_function
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T)
      (arg: v_T)
    : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = ["used_only_from_this_lib_crate_generic_function with "; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #v_T arg <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()

let used_from_bin_crate_and_lib_crate_generic_function
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T)
      (arg: v_T)
    : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = ["used_from_bin_crate_and_lib_crate_generic_function with "; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #v_T arg <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()

let used_with_same_type_from_bin_crate_and_lib_crate_generic_function
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T)
      (arg: v_T)
    : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list =
              ["used_with_same_type_from_bin_crate_and_lib_crate_generic_function with "; "\n"]
            in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #v_T arg <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()

let unused_generic_function
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Fmt.t_Debug v_T)
      (arg: v_T)
    : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = ["unused_generic_function with "; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #v_T arg <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()

let unused_function (_: Prims.unit) : Prims.unit =
  let is_true:bool =
    (Core.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let countdown:i32 = mk_i32 2 in
  if ~.is_true
  then
    let countdown:i32 = mk_i32 20 in
    ()

let unused_private_function (_: Prims.unit) : Prims.unit =
  let is_true:bool =
    (Core.Iter.Traits.Exact_size.f_len #Std.Env.t_Args
        #FStar.Tactics.Typeclasses.solve
        (Std.Env.args () <: Std.Env.t_Args)
      <:
      usize) =.
    mk_usize 1
  in
  let countdown:i32 = mk_i32 2 in
  if ~.is_true
  then
    let countdown:i32 = mk_i32 20 in
    ()

let uuse_this_lib_crate (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    used_from_bin_crate_and_lib_crate_generic_function #string "used from library used_crate.rs"
  in
  let _:Prims.unit =
    used_with_same_type_from_bin_crate_and_lib_crate_generic_function #string
      "used from library used_crate.rs"
  in
  let some_vec:Alloc.Vec.t_Vec i32 Alloc.Alloc.t_Global =
    Alloc.Slice.impl__into_vec #i32
      #Alloc.Alloc.t_Global
      (Rust_primitives.unsize (Rust_primitives.Hax.box_new (let list =
                  [mk_i32 5; mk_i32 6; mk_i32 7; mk_i32 8]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
                Rust_primitives.Hax.array_of_list 4 list)
            <:
            Alloc.Boxed.t_Box (t_Array i32 (mk_usize 4)) Alloc.Alloc.t_Global)
        <:
        Alloc.Boxed.t_Box (t_Slice i32) Alloc.Alloc.t_Global)
  in
  let _:Prims.unit =
    used_only_from_this_lib_crate_generic_function #(Alloc.Vec.t_Vec i32 Alloc.Alloc.t_Global)
      some_vec
  in
  let _:Prims.unit =
    used_only_from_this_lib_crate_generic_function #string "used ONLY from library used_crate.rs"
  in
  ()

let used_function (_: Prims.unit) : Prims.unit =
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
  let _:Prims.unit = uuse_this_lib_crate () in
  ()

let used_inline_function (_: Prims.unit) : Prims.unit =
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
  let _:Prims.unit = uuse_this_lib_crate () in
  ()
