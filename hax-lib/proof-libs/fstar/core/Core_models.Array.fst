module Core_models.Array
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_TryFromSliceError = | TryFromSliceError : t_TryFromSliceError

let impl_23__map
      (#v_T: Type0)
      (v_N: usize)
      (#v_F #v_U: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_T)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_U})
      (s: t_Array v_T v_N)
      (f: v_F)
    : t_Array v_U v_N = Rust_primitives.Slice.array_map #v_T #v_U v_N #v_F s f

let impl_23__as_slice (#v_T: Type0) (v_N: usize) (s: t_Array v_T v_N) : t_Slice v_T =
  Rust_primitives.Slice.array_as_slice #v_T v_N s

let from_fn
      (#v_T: Type0)
      (v_N: usize)
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F usize)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (f: v_F)
    : t_Array v_T v_N = Rust_primitives.Slice.array_from_fn #v_T v_N #v_F f

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24 (#v_T: Type0) (v_N: usize)
    : Core_models.Iter.Traits.Collect.t_IntoIterator (t_Array v_T v_N) =
  {
    f_IntoIter = Core_models.Array.Iter.t_IntoIter v_T v_N;
    f_into_iter_pre = (fun (self: t_Array v_T v_N) -> true);
    f_into_iter_post
    =
    (fun (self: t_Array v_T v_N) (out: Core_models.Array.Iter.t_IntoIter v_T v_N) -> true);
    f_into_iter
    =
    fun (self: t_Array v_T v_N) ->
      Core_models.Array.Iter.IntoIter (Rust_primitives.Sequence.seq_from_array #v_T v_N self)
      <:
      Core_models.Array.Iter.t_IntoIter v_T v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25 (#v_T: Type0) (v_N: usize) : Core_models.Ops.Index.t_Index (t_Array v_T v_N) usize =
  {
    f_Output = v_T;
    f_index_pre
    =
    (fun (self_: t_Array v_T v_N) (i: usize) ->
        i <. (Core_models.Slice.impl__len #v_T (self_ <: t_Slice v_T) <: usize));
    f_index_post = (fun (self: t_Array v_T v_N) (i: usize) (out: v_T) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (i: usize) -> Rust_primitives.Slice.array_index #v_T v_N self i
  }
