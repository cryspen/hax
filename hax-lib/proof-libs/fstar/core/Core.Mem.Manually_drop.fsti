module Core.Mem.Manually_drop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_ManuallyDrop (v_T: Type0) = { f_value:v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6 (#v_T: Type0) {| i0: Core.Clone.t_Clone v_T |} : Core.Clone.t_Clone (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5 (#v_T: Type0) {| i0: Core.Marker.t_Copy v_T |} : Core.Marker.t_Copy (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7 (#v_T: Type0) {| i0: Core.Fmt.t_Debug v_T |} : Core.Fmt.t_Debug (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8 (#v_T: Type0) {| i0: Core.Default.t_Default v_T |}
    : Core.Default.t_Default (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9 (#v_T: Type0) : Core.Marker.t_StructuralPartialEq (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10 (#v_T: Type0) {| i0: Core.Cmp.t_PartialEq v_T v_T |}
    : Core.Cmp.t_PartialEq (t_ManuallyDrop v_T) (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_11 (#v_T: Type0) {| i0: Core.Cmp.t_Eq v_T |} : Core.Cmp.t_Eq (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_12 (#v_T: Type0) {| i0: Core.Cmp.t_PartialOrd v_T v_T |}
    : Core.Cmp.t_PartialOrd (t_ManuallyDrop v_T) (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_13 (#v_T: Type0) {| i0: Core.Cmp.t_Ord v_T |} : Core.Cmp.t_Ord (t_ManuallyDrop v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_14 (#v_T: Type0) {| i0: Core.Hash.t_Hash v_T |} : Core.Hash.t_Hash (t_ManuallyDrop v_T)

val impl__new (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (value: v_T)
    : Prims.Pure (t_ManuallyDrop v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl__into_inner (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (slot: t_ManuallyDrop v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

val impl__take (#v_T: Type0) {| i0: Core.Marker.t_Sized v_T |} (slot: t_ManuallyDrop v_T)
    : Prims.Pure (t_ManuallyDrop v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl__take__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val impl_1__drop (#v_T: Type0) (slot: t_ManuallyDrop v_T)
    : Prims.Pure (t_ManuallyDrop v_T) Prims.l_True (fun _ -> Prims.l_True)

val impl_1__drop__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Core.Ops.Deref.t_Deref (t_ManuallyDrop v_T) =
  {
    f_Target = v_T;
    f_deref_pre = (fun (self: t_ManuallyDrop v_T) -> true);
    f_deref_post = (fun (self: t_ManuallyDrop v_T) (out: v_T) -> true);
    f_deref = fun (self: t_ManuallyDrop v_T) -> () <: v_T
  }

val f_deref__impl_2__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_3 (#v_T: Type0) : Core.Ops.Deref.t_DerefMut (t_ManuallyDrop v_T)

val f_deref_mut__impl_3__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_4 (#v_T: Type0) : Core.Ops.Deref.t_DerefPure (t_ManuallyDrop v_T)
