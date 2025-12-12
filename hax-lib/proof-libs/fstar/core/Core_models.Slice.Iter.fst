module Core_models.Slice.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Chunks (v_T: Type0) = | Chunks : Rust_primitives.Sequence.t_Seq v_T -> t_Chunks v_T

type t_ChunksExact (v_T: Type0) =
  | ChunksExact : Rust_primitives.Sequence.t_Seq v_T -> t_ChunksExact v_T

type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Iter v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Iter v_T) -> true);
    f_next_post
    =
    (fun (self: t_Iter v_T) (out: (t_Iter v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Iter v_T) ->
      let (self: t_Iter v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Iter v_T & Core_models.Option.t_Option v_T)
        else
          let res:v_T = Rust_primitives.Sequence.seq_first #v_T self._0 in
          let self:t_Iter v_T =
            {
              self with
              _0
              =
              Rust_primitives.Sequence.seq_slice #v_T
                self._0
                (mk_usize 1)
                (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize)
            }
            <:
            t_Iter v_T
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option v_T)
          <:
          (t_Iter v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Iter v_T & Core_models.Option.t_Option v_T)
  }
