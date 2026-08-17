module Core_models.Iter.Sources.Once
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Once`]
type t_Once (v_T: Type0) = | Once : Rust_primitives.Sequence.t_Seq v_T -> t_Once v_T

/// See [`std::iter::once`]
let once (#v_T: Type0) (value: v_T) : t_Once v_T =
  Once (Rust_primitives.Sequence.seq_one #v_T value) <: t_Once v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Once v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Once v_T) -> true);
    f_next_post
    =
    (fun (self: t_Once v_T) (out1: (t_Once v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Once v_T) ->
      let (self: t_Once v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Once v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Once v_T = { self with _0 = tmp0 } <: t_Once v_T in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_Once v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Once v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : Core_models.Iter.Traits.Double_ended.t_DoubleEndedIterator (t_Once v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_next_back_pre = (fun (self: t_Once v_T) -> true);
    f_next_back_post
    =
    (fun (self: t_Once v_T) (out1: (t_Once v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next_back
    =
    fun (self: t_Once v_T) ->
      let n:usize = Rust_primitives.Sequence.seq_len #v_T self._0 in
      let (self: t_Once v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if n =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Once v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (n -! mk_usize 1 <: usize)
          in
          let self:t_Once v_T = { self with _0 = tmp0 } <: t_Once v_T in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_Once v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Once v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Core_models.Iter.Traits.Exact_size.t_ExactSizeIterator (t_Once v_T) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_len_pre = (fun (self: t_Once v_T) -> true);
    f_len_post = (fun (self: t_Once v_T) (out: usize) -> true);
    f_len = fun (self: t_Once v_T) -> Rust_primitives.Sequence.seq_len #v_T self._0
  }
