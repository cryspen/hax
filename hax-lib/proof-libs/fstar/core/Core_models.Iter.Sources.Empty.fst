module Core_models.Iter.Sources.Empty
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Empty`]
type t_Empty (v_T: Type0) = | Empty : Rust_primitives.Sequence.t_Seq v_T -> t_Empty v_T

/// See [`std::iter::empty`]
let empty (#v_T: Type0) (_: Prims.unit) : t_Empty v_T =
  Empty (Rust_primitives.Sequence.seq_empty #v_T ()) <: t_Empty v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Empty v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Empty v_T) -> true);
    f_next_post
    =
    (fun (self: t_Empty v_T) (out: (t_Empty v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Empty v_T) ->
      let hax_temp_output:Core_models.Option.t_Option v_T =
        Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
      in
      self, hax_temp_output <: (t_Empty v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator (t_Empty v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: t_Empty v_T) -> true);
    f_next_back_post
    =
    (fun (self: t_Empty v_T) (out: (t_Empty v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next_back
    =
    fun (self: t_Empty v_T) ->
      let hax_temp_output:Core_models.Option.t_Option v_T =
        Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
      in
      self, hax_temp_output <: (t_Empty v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator (t_Empty v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: t_Empty v_T) -> true);
    f_len_post = (fun (self: t_Empty v_T) (out: usize) -> true);
    f_len = fun (self: t_Empty v_T) -> mk_usize 0
  }
