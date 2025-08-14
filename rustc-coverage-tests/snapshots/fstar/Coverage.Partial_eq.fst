module Coverage.Partial_eq
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Version = {
  f_major:usize;
  f_minor:usize;
  f_patch:usize
}

let impl_1: Core.Clone.t_Clone t_Version =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Fmt.t_Debug t_Version

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Marker.t_StructuralPartialEq t_Version

unfold
let impl_3 = impl_3'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Cmp.t_PartialEq t_Version t_Version

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Cmp.t_Eq t_Version

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core.Cmp.t_PartialOrd t_Version t_Version

unfold
let impl_6 = impl_6'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Cmp.t_Ord t_Version

unfold
let impl_7 = impl_7'

let impl_Version__new (major minor patch: usize) : t_Version =
  { f_major = major; f_minor = minor; f_patch = patch } <: t_Version

let main (_: Prims.unit) : Prims.unit =
  let version_3_2_1_:t_Version = impl_Version__new (mk_usize 3) (mk_usize 2) (mk_usize 1) in
  let version_3_3_0_:t_Version = impl_Version__new (mk_usize 3) (mk_usize 3) (mk_usize 0) in
  let args:(t_Version & t_Version & bool) =
    version_3_2_1_,
    version_3_3_0_,
    Core.Cmp.f_lt #t_Version
      #t_Version
      #FStar.Tactics.Typeclasses.solve
      version_3_2_1_
      version_3_3_0_
    <:
    (t_Version & t_Version & bool)
  in
  let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 3) =
    let list =
      [
        Core.Fmt.Rt.impl__new_debug #t_Version args._1;
        Core.Fmt.Rt.impl__new_debug #t_Version args._2;
        Core.Fmt.Rt.impl__new_display #bool args._3
      ]
    in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 3);
    Rust_primitives.Hax.array_of_list 3 list
  in
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 4)
          (mk_usize 3)
          (let list = [""; " < "; " = "; "\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
            Rust_primitives.Hax.array_of_list 4 list)
          args
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()
