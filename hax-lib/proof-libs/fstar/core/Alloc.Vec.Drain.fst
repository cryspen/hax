module Alloc.Vec.Drain
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Drain (v_T: Type0) (v_A: Type0) =
  | Drain : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_Drain v_T v_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T #v_A: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Drain v_T v_A) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Drain v_T v_A) -> true);
    f_next_post
    =
    (fun (self: t_Drain v_T v_A) (out: (t_Drain v_T v_A & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Drain v_T v_A) ->
      let (self: t_Drain v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Drain v_T v_A & Core_models.Option.t_Option v_T)
        else
          let res:v_T = Rust_primitives.Sequence.seq_first #v_T self._0 in
          let self:t_Drain v_T v_A =
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
            t_Drain v_T v_A
          in
          self, (Core_models.Option.Option_Some res <: Core_models.Option.t_Option v_T)
          <:
          (t_Drain v_T v_A & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Drain v_T v_A & Core_models.Option.t_Option v_T)
  }
