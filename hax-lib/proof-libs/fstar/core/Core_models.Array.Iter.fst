module Core_models.Array.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_IntoIter (v_T: Type0) (v_N: usize) =
  | IntoIter : Rust_primitives.Sequence.t_Seq v_T -> t_IntoIter v_T v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (v_N: usize)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_IntoIter v_T v_N) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_IntoIter v_T v_N) -> true);
    f_next_post
    =
    (fun (self: t_IntoIter v_T v_N) (out: (t_IntoIter v_T v_N & Core_models.Option.t_Option v_T)) ->
        true);
    f_next
    =
    fun (self: t_IntoIter v_T v_N) ->
      let (self: t_IntoIter v_T v_N), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_IntoIter v_T v_N & Core_models.Option.t_Option v_T)
        else
          let res:v_T = Rust_primitives.Sequence.seq_first #v_T self._0 in
          let self:t_IntoIter v_T v_N =
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
            t_IntoIter v_T v_N
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option v_T)
          <:
          (t_IntoIter v_T v_N & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_IntoIter v_T v_N & Core_models.Option.t_Option v_T)
  }
