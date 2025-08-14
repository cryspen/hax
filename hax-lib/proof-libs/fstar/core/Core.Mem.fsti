module Core.Mem
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

val forget (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (t: v_T)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val forget_unsized (#v_T: Type0) (t: v_T)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val size_of: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val size_of_val (#v_T: Type0) (v_val: v_T) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val min_align_of: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val min_align_of_val (#v_T: Type0) (v_val: v_T)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val align_of: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val align_of_val (#v_T: Type0) (v_val: v_T) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)


val needs_drop: #v_T: Type0 -> Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

val zeroed: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val uninitialized: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val swap (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (x y: v_T)
    : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val take
      (#v_T: Type0)
      {| i0: Core.Marker.t_Sized v_T |}
      {| i1: Core.Default.t_Default v_T |}
      (dest: v_T)
    : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val replace (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (dest src: v_T)
    : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val drop (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (e_x: v_T)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

val copy (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} {| i1: Core.Marker.t_Copy v_T |} (x: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val transmute_copy
      (#v_Src #v_Dst: Type0)
      {| i0: Core.Marker.t_Sized v_Src |}
      {| i1: Core.Marker.t_Sized v_Dst |}
      (src: v_Src)
    : Prims.Pure v_Dst Prims.l_True (fun _ -> Prims.l_True)

(* type t_Discriminant (v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} =
  | Discriminant : _ -> t_Discriminant v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Clone.t_Clone (t_Discriminant v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Marker.t_Copy (t_Discriminant v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_2 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |}
    : Core.Cmp.t_PartialEq (t_Discriminant v_T) (t_Discriminant v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Cmp.t_Eq (t_Discriminant v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Hash.t_Hash (t_Discriminant v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5 (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} : Core.Fmt.t_Debug (t_Discriminant v_T)

val discriminant (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (v: v_T)
    : Prims.Pure (t_Discriminant v_T) Prims.l_True (fun _ -> Prims.l_True) *)

val variant_count: #v_T: Type0 -> {| i0: Core.Marker.t_Sized v_T |} -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

