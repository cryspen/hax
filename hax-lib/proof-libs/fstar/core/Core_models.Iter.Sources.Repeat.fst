module Core_models.Iter.Sources.Repeat
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Repeat`]
type t_Repeat (v_A: Type0) = { f_element:v_A }

/// See [`std::iter::repeat`]
let repeat
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
      (elt: v_A)
    : t_Repeat v_A = { f_element = elt } <: t_Repeat v_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_A: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_Repeat v_A) =
  {
    f_Item = v_A;
    f_next_pre = (fun (self: t_Repeat v_A) -> true);
    f_next_post
    =
    (fun (self: t_Repeat v_A) (out: (t_Repeat v_A & Core_models.Option.t_Option v_A)) -> true);
    f_next
    =
    fun (self: t_Repeat v_A) ->
      let hax_temp_output:Core_models.Option.t_Option v_A =
        Core_models.Option.Option_Some
        (Core_models.Clone.f_clone #v_A #FStar.Tactics.Typeclasses.solve self.f_element)
        <:
        Core_models.Option.t_Option v_A
      in
      self, hax_temp_output <: (t_Repeat v_A & Core_models.Option.t_Option v_A)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator (t_Repeat v_A) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: t_Repeat v_A) -> true);
    f_next_back_post
    =
    (fun (self: t_Repeat v_A) (out: (t_Repeat v_A & Core_models.Option.t_Option v_A)) -> true);
    f_next_back
    =
    fun (self: t_Repeat v_A) ->
      let hax_temp_output:Core_models.Option.t_Option v_A =
        Core_models.Option.Option_Some
        (Core_models.Clone.f_clone #v_A #FStar.Tactics.Typeclasses.solve self.f_element)
        <:
        Core_models.Option.t_Option v_A
      in
      self, hax_temp_output <: (t_Repeat v_A & Core_models.Option.t_Option v_A)
  }
