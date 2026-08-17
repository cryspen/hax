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
