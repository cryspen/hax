module Core_models.Iter.Sources.Repeat_n
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::RepeatN`]
type t_RepeatN (v_A: Type0) = {
  f_count:usize;
  f_element:v_A
}

/// See [`std::iter::repeat_n`]
let repeat_n
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
      (element: v_A)
      (count: usize)
    : t_RepeatN v_A = { f_count = count; f_element = element } <: t_RepeatN v_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_A: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_RepeatN v_A) =
  {
    f_Item = v_A;
    f_next_pre = (fun (self: t_RepeatN v_A) -> true);
    f_next_post
    =
    (fun (self: t_RepeatN v_A) (out: (t_RepeatN v_A & Core_models.Option.t_Option v_A)) -> true);
    f_next
    =
    fun (self: t_RepeatN v_A) ->
      let (self: t_RepeatN v_A), (hax_temp_output: Core_models.Option.t_Option v_A) =
        if self.f_count =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_A)
          <:
          (t_RepeatN v_A & Core_models.Option.t_Option v_A)
        else
          let self:t_RepeatN v_A =
            { self with f_count = self.f_count -! mk_usize 1 } <: t_RepeatN v_A
          in
          self,
          (Core_models.Option.Option_Some
            (Core_models.Clone.f_clone #v_A #FStar.Tactics.Typeclasses.solve self.f_element)
            <:
            Core_models.Option.t_Option v_A)
          <:
          (t_RepeatN v_A & Core_models.Option.t_Option v_A)
      in
      self, hax_temp_output <: (t_RepeatN v_A & Core_models.Option.t_Option v_A)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator (t_RepeatN v_A) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: t_RepeatN v_A) -> true);
    f_next_back_post
    =
    (fun (self: t_RepeatN v_A) (out1: (t_RepeatN v_A & Core_models.Option.t_Option v_A)) -> true);
    f_next_back
    =
    fun (self: t_RepeatN v_A) ->
      let (tmp0: t_RepeatN v_A), (out: Core_models.Option.t_Option v_A) =
        Core_models.Iter.Traits.Iterator.f_next #(t_RepeatN v_A)
          #FStar.Tactics.Typeclasses.solve
          self
      in
      let self:t_RepeatN v_A = tmp0 in
      let hax_temp_output:Core_models.Option.t_Option v_A = out in
      self, hax_temp_output <: (t_RepeatN v_A & Core_models.Option.t_Option v_A)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
    : Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator (t_RepeatN v_A) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: t_RepeatN v_A) -> true);
    f_len_post = (fun (self: t_RepeatN v_A) (out: usize) -> true);
    f_len = fun (self: t_RepeatN v_A) -> self.f_count
  }
