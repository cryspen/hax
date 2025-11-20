module Alloc.Collections.Vec_deque
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_VecDeque (v_T: Type0) (v_A: Type0) =
  | VecDeque : Rust_primitives.Seq.t_Seq v_T v_A -> t_VecDeque v_T v_A

val impl_5__push_back (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (x: v_T)
    : Prims.Pure (t_VecDeque v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

val impl_5__len (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

val impl_5__pop_front (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A)
    : Prims.Pure (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_T #v_A: Type0) : Core_models.Ops.Index.t_Index (t_VecDeque v_T v_A) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (self: t_VecDeque v_T v_A) (i: usize) -> true);
    f_index_post = (fun (self: t_VecDeque v_T v_A) (i: usize) (out: v_T) -> true);
    f_index
    =
    fun (self: t_VecDeque v_T v_A) (i: usize) -> Rust_primitives.Seq.seq_index #v_T #v_A self._0 i
  }
