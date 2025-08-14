module Core.Mem.Transmutability
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul


val f_transmute__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

type t_Assume = {
  f_alignment:bool;
  f_lifetimes:bool;
  f_safety:bool;
  f_validity:bool
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_5:Core.Marker.t_StructuralPartialEq t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_6:Core.Cmp.t_PartialEq t_Assume t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_7:Core.Cmp.t_Eq t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_8:Core.Clone.t_Clone t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_9:Core.Marker.t_Copy t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_10:Core.Fmt.t_Debug t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl_1:Core.Marker.t_UnsizedConstParamTy t_Assume

[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core.Marker.t_ConstParamTy_ t_Assume

let impl_Assume__NOTHING: t_Assume = () <: t_Assume

let impl_Assume__ALIGNMENT: t_Assume = () <: t_Assume

let impl_Assume__LIFETIMES: t_Assume = () <: t_Assume

let impl_Assume__SAFETY: t_Assume = () <: t_Assume

let impl_Assume__VALIDITY: t_Assume = () <: t_Assume

val impl_Assume__and (self other_assumptions: t_Assume)
    : Prims.Pure t_Assume Prims.l_True (fun _ -> Prims.l_True)

val impl_Assume__but_not (self other_assumptions: t_Assume)
    : Prims.Pure t_Assume Prims.l_True (fun _ -> Prims.l_True)

val f_add__impl_3__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

val f_sub__impl_4__panic_cold_explicit: Prims.unit
  -> Prims.Pure Rust_primitives.Hax.t_Never Prims.l_True (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Add t_Assume t_Assume =
  {
    f_Output = t_Assume;
    f_Output_11695847888444666345 = FStar.Tactics.Typeclasses.solve;
    f_add_pre = (fun (self: t_Assume) (other_assumptions: t_Assume) -> true);
    f_add_post = (fun (self: t_Assume) (other_assumptions: t_Assume) (out: t_Assume) -> true);
    f_add = fun (self: t_Assume) (other_assumptions: t_Assume) -> () <: t_Assume
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Ops.Arith.t_Sub t_Assume t_Assume =
  {
    f_Output = t_Assume;
    f_Output_9381071510542709353 = FStar.Tactics.Typeclasses.solve;
    f_sub_pre = (fun (self: t_Assume) (other_assumptions: t_Assume) -> true);
    f_sub_post = (fun (self: t_Assume) (other_assumptions: t_Assume) (out: t_Assume) -> true);
    f_sub = fun (self: t_Assume) (other_assumptions: t_Assume) -> () <: t_Assume
  }
