module Tests.Legacy__naming.Ambiguous_names
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// @fail(extraction): ssprove(HAX0001)
let debug (label value: u32) : Prims.unit =
  let args:(u32 & u32) = label, value <: (u32 & u32) in
  let args:t_Array Core_models.Fmt.Rt.t_Argument (mk_usize 2) =
    let list =
      [
        Core_models.Fmt.Rt.impl__new_display #u32 args._1;
        Core_models.Fmt.Rt.impl__new_display #u32 args._2
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
    Rust_primitives.Hax.array_of_list 2 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_v1 (mk_usize 3)
          (mk_usize 2)
          (let list = ["["; "] a="; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
            Rust_primitives.Hax.array_of_list 3 list)
          args
        <:
        Core_models.Fmt.t_Arguments)
  in
  ()

/// `f` stacks mutliple let bindings declaring different `a`s.
let f (_: Prims.unit) : Prims.unit =
  let a_1_:u32 = mk_u32 104 in
  let a_2_:u32 = mk_u32 205 in
  let a_3_:u32 = mk_u32 306 in
  let a:u32 = mk_u32 123 in
  let _:Prims.unit = debug (mk_u32 3) a_3_ in
  let _:Prims.unit = debug (mk_u32 2) a_2_ in
  let _:Prims.unit = debug (mk_u32 1) a_1_ in
  debug (mk_u32 4) a

/// `f` is expanded into `f_expand` below, while the execution of `f` gives:
/// ```plaintext
///  [3] a=306
///  [2] a=205
///  [1] a=104
///  [last] a=123
/// ```
let ff_expand (_: Prims.unit) : Prims.unit =
  let a:i32 = mk_i32 104 in
  let a:i32 = mk_i32 205 in
  let a:i32 = mk_i32 306 in
  let a:u32 = mk_u32 123 in
  let _:Prims.unit = debug (mk_u32 3) a in
  let _:Prims.unit = debug (mk_u32 2) a in
  let _:Prims.unit = debug (mk_u32 1) a in
  debug (mk_u32 0) a
