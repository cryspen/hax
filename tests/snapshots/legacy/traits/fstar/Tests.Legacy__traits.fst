module Tests.Legacy__traits
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_SuperTrait (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_14156401398203956914:Core.Clone.t_Clone v_Self;
  f_function_of_super_trait_pre:v_Self -> Type0;
  f_function_of_super_trait_post:v_Self -> u32 -> Type0;
  f_function_of_super_trait:x0: v_Self
    -> Prims.Pure u32
        (f_function_of_super_trait_pre x0)
        (fun result -> f_function_of_super_trait_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_SuperTrait v_Self|} -> i._super_14156401398203956914

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_SuperTrait i32 =
  {
    _super_14156401398203956914 = FStar.Tactics.Typeclasses.solve;
    f_function_of_super_trait_pre = (fun (self: i32) -> true);
    f_function_of_super_trait_post = (fun (self: i32) (out: u32) -> true);
    f_function_of_super_trait = fun (self: i32) -> cast (Core.Num.impl_i32__abs self <: i32) <: u32
  }

type t_Struct = | Struct : t_Struct

class t_Bar (v_Self: Type0) = {
  f_bar_pre:v_Self -> Type0;
  f_bar_post:v_Self -> Prims.unit -> Type0;
  f_bar:x0: v_Self -> Prims.Pure Prims.unit (f_bar_pre x0) (fun result -> f_bar_post x0 result)
}

let impl_2__method (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Bar v_T) (x: v_T)
    : Prims.unit = f_bar #v_T #FStar.Tactics.Typeclasses.solve x

let cclosure_iimpl_expr
      (#v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Iter.Traits.Iterator.t_Iterator v_I)
      (it: v_I)
    : Alloc.Vec.t_Vec Prims.unit Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map v_I (Prims.unit -> Prims.unit))
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec Prims.unit Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_map #v_I
        #FStar.Tactics.Typeclasses.solve
        #Prims.unit
        it
        (fun x -> x)
      <:
      Core.Iter.Adapters.Map.t_Map v_I (Prims.unit -> Prims.unit))

let cclosure_iimpl_expr_fngen
      (#v_I #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Iter.Traits.Iterator.t_Iterator v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Ops.Function.t_FnMut v_F Prims.unit)
      (it: v_I)
      (f: v_F)
    : Alloc.Vec.t_Vec Prims.unit Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.f_collect #(Core.Iter.Adapters.Map.t_Map v_I v_F)
    #FStar.Tactics.Typeclasses.solve
    #(Alloc.Vec.t_Vec Prims.unit Alloc.Alloc.t_Global)
    (Core.Iter.Traits.Iterator.f_map #v_I #FStar.Tactics.Typeclasses.solve #Prims.unit #v_F it f
      <:
      Core.Iter.Adapters.Map.t_Map v_I v_F)

type t_Error = | Error_Fail : t_Error

let t_Error_cast_to_repr (x: t_Error) : isize = match x <: t_Error with | Error_Fail  -> mk_isize 0

let impl_Error__for_application_callback (_: Prims.unit) :  Prims.unit -> t_Error =
  fun temp_0_ ->
    let _:Prims.unit = temp_0_ in
    Error_Fail <: t_Error

let iter_option (#v_T: Type0) (x: Core.Option.t_Option v_T) : Core.Option.t_IntoIter v_T =
  Core.Iter.Traits.Collect.f_into_iter #(Core.Option.t_Option v_T)
    #FStar.Tactics.Typeclasses.solve
    (Core.Option.impl__as_ref #v_T x <: Core.Option.t_Option v_T)

let uuse_iimpl_trait (_: Prims.unit) : Prims.unit =
  let iter:Core.Option.t_IntoIter bool =
    iter_option #bool (Core.Option.Option_Some false <: Core.Option.t_Option bool)
  in
  let tmp0, out:(Core.Option.t_IntoIter bool & Core.Option.t_Option bool) =
    Core.Iter.Traits.Iterator.f_next #(Core.Option.t_IntoIter bool)
      #FStar.Tactics.Typeclasses.solve
      iter
  in
  let iter:Core.Option.t_IntoIter bool = tmp0 in
  let _:Core.Option.t_Option bool = out in
  ()

class t_Foo (v_Self: Type0) = {
  f_AssocType:Type0;
  f_AssocType_13701427516003292911:t_SuperTrait f_AssocType;
  f_N:usize;
  f_assoc_f_pre:Prims.unit -> Type0;
  f_assoc_f_post:Prims.unit -> Prims.unit -> Type0;
  f_assoc_f:x0: Prims.unit
    -> Prims.Pure Prims.unit (f_assoc_f_pre x0) (fun result -> f_assoc_f_post x0 result);
  f_method_f_pre:v_Self -> Type0;
  f_method_f_post:v_Self -> Prims.unit -> Type0;
  f_method_f:x0: v_Self
    -> Prims.Pure Prims.unit (f_method_f_pre x0) (fun result -> f_method_f_post x0 result);
  f_assoc_type_pre:{| i1: Core.Marker.t_Copy f_AssocType |} -> f_AssocType -> Type0;
  f_assoc_type_post:{| i1: Core.Marker.t_Copy f_AssocType |} -> f_AssocType -> Prims.unit -> Type0;
  f_assoc_type:{| i1: Core.Marker.t_Copy f_AssocType |} -> x0: f_AssocType
    -> Prims.Pure Prims.unit
        (f_assoc_type_pre #i1 x0)
        (fun result -> f_assoc_type_post #i1 x0 result)
}

class t_Lang (v_Self: Type0) = {
  f_Var:Type0;
  f_s_pre:v_Self -> i32 -> Type0;
  f_s_post:v_Self -> i32 -> (v_Self & f_Var) -> Type0;
  f_s:x0: v_Self -> x1: i32
    -> Prims.Pure (v_Self & f_Var) (f_s_pre x0 x1) (fun result -> f_s_post x0 x1 result)
}

let f (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Foo v_T) (x: v_T) : Prims.unit =
  let _:Prims.unit = f_assoc_f #v_T #FStar.Tactics.Typeclasses.solve () in
  f_method_f #v_T #FStar.Tactics.Typeclasses.solve x

let g (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Foo v_T) (x: i0.f_AssocType)
    : u32 = f_function_of_super_trait #i0.f_AssocType #FStar.Tactics.Typeclasses.solve x

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Foo_for_tuple_: t_Foo Prims.unit =
  {
    f_AssocType = i32;
    f_AssocType_13701427516003292911 = FStar.Tactics.Typeclasses.solve;
    f_N = mk_usize 32;
    f_assoc_f_pre = (fun (_: Prims.unit) -> true);
    f_assoc_f_post = (fun (_: Prims.unit) (out: Prims.unit) -> true);
    f_assoc_f = (fun (_: Prims.unit) -> () <: Prims.unit);
    f_method_f_pre = (fun (self: Prims.unit) -> true);
    f_method_f_post = (fun (self: Prims.unit) (out: Prims.unit) -> true);
    f_method_f
    =
    (fun (self: Prims.unit) -> f_assoc_f #Prims.unit #FStar.Tactics.Typeclasses.solve ());
    f_assoc_type_pre = (fun (_: i32) -> true);
    f_assoc_type_post = (fun (_: i32) (out: Prims.unit) -> true);
    f_assoc_type = fun (_: i32) -> ()
  }
