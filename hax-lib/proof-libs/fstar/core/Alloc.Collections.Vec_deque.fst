module Alloc.Collections.Vec_deque
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_VecDeque (v_T: Type0) (v_A: Type0) =
  | VecDeque : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_VecDeque v_T v_A

assume
val impl_5__push_back': #v_T: Type0 -> #v_A: Type0 -> self: t_VecDeque v_T v_A -> x: v_T
  -> t_VecDeque v_T v_A

unfold
let impl_5__push_back (#v_T #v_A: Type0) = impl_5__push_back' #v_T #v_A

let impl_5__len (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : usize =
  Rust_primitives.Sequence.seq_len #v_T self._0

let impl_5__pop_front (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A)
    : (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T) =
  let (self: t_VecDeque v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if (impl_5__len #v_T #v_A self <: usize) =. mk_usize 0
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
    else
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_T #v_A: Type0) : Core_models.Ops.Index.t_Index (t_VecDeque v_T v_A) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (self: t_VecDeque v_T v_A) (i: usize) -> true);
    f_index_post = (fun (self: t_VecDeque v_T v_A) (i: usize) (out: v_T) -> true);
    f_index
    =
    fun (self: t_VecDeque v_T v_A) (i: usize) -> Rust_primitives.Sequence.seq_index #v_T self._0 i
  }
