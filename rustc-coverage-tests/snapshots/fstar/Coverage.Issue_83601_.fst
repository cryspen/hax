module Coverage.Issue_83601_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Foo = | Foo : u32 -> t_Foo

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl': Core.Fmt.t_Debug t_Foo

unfold
let impl = impl'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_StructuralPartialEq t_Foo

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Cmp.t_PartialEq t_Foo t_Foo

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Cmp.t_Eq t_Foo

unfold
let impl_3 = impl_3'

let main (_: Prims.unit) : Prims.unit =
  let bar:t_Foo = Foo (mk_u32 1) <: t_Foo in
  let _:Prims.unit =
    match bar, (Foo (mk_u32 1) <: t_Foo) <: (t_Foo & t_Foo) with
    | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
  in
  let baz:t_Foo = Foo (mk_u32 0) <: t_Foo in
  let _:Prims.unit =
    match baz, (Foo (mk_u32 1) <: t_Foo) <: (t_Foo & t_Foo) with
    | left_val, right_val -> Hax_lib.v_assert (~.(left_val =. right_val <: bool) <: bool)
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list =
              [
                Core.Fmt.Rt.impl__new_debug #t_Foo (Foo (mk_u32 1) <: t_Foo)
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
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #t_Foo bar <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_v1 (mk_usize 2)
          (mk_usize 1)
          (let list = [""; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
            Rust_primitives.Hax.array_of_list 2 list)
          (let list = [Core.Fmt.Rt.impl__new_debug #t_Foo baz <: Core.Fmt.Rt.t_Argument] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()
