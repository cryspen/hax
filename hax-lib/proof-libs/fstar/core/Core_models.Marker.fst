module Core_models.Marker
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

class t_Copy (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:Core_models.Clone.t_Clone v_Self
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_Copy v_Self|} -> i._super_i0

class t_Send (v_Self: Type0) = { __marker_trait_t_Send:Prims.unit }

class t_Sync (v_Self: Type0) = { __marker_trait_t_Sync:Prims.unit }

class t_Sized (v_Self: Type0) = { __marker_trait_t_Sized:Prims.unit }

class t_StructuralPartialEq (v_Self: Type0) = { __marker_trait_t_StructuralPartialEq:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_Send v_T = { __marker_trait_t_Send = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : t_Sync v_T = { __marker_trait_t_Sync = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : t_Sized v_T = { __marker_trait_t_Sized = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
    : t_Copy v_T = { _super_i0 = FStar.Tactics.Typeclasses.solve }

type t_PhantomData (v_T: Type0) = | PhantomData : t_PhantomData v_T
