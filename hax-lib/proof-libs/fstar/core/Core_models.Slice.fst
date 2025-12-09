module Core_models.Slice
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

let impl__len (#v_T: Type0) (s: t_Slice v_T) : usize = Rust_primitives.Slice.slice_length #v_T s

assume
val impl__chunks': #v_T: Type0 -> s: t_Slice v_T -> cs: usize -> Core_models.Slice.Iter.t_Chunks v_T

unfold
let impl__chunks (#v_T: Type0) = impl__chunks' #v_T

let impl__iter (#v_T: Type0) (s: t_Slice v_T) : Core_models.Slice.Iter.t_Iter v_T = s

assume
val impl__chunks_exact': #v_T: Type0 -> s: t_Slice v_T -> cs: usize
  -> Core_models.Slice.Iter.t_ChunksExact v_T

unfold
let impl__chunks_exact (#v_T: Type0) = impl__chunks_exact' #v_T

let impl__is_empty (#v_T: Type0) (s: t_Slice v_T) : bool = (impl__len #v_T s <: usize) =. mk_usize 0

assume
val impl__contains': #v_T: Type0 -> s: t_Slice v_T -> v: v_T -> bool

unfold
let impl__contains (#v_T: Type0) = impl__contains' #v_T

assume
val impl__copy_within':
    #v_T: Type0 ->
    #v_R: Type0 ->
    {| i0: Core_models.Marker.t_Copy v_T |} ->
    s: t_Slice v_T ->
    src: v_R ->
    dest: usize
  -> t_Slice v_T

unfold
let impl__copy_within
      (#v_T #v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
     = impl__copy_within' #v_T #v_R #i0

assume
val impl__binary_search': #v_T: Type0 -> s: t_Slice v_T -> x: v_T
  -> Core_models.Result.t_Result usize usize

unfold
let impl__binary_search (#v_T: Type0) = impl__binary_search' #v_T

assume
val impl__get':
    #v_T: Type0 ->
    #v_I: Type0 ->
    {| i0: Core_models.Ops.Index.t_Index (t_Slice v_T) v_I |} ->
    s: t_Slice v_T ->
    i: v_I
  -> Core_models.Option.t_Option i0.f_Output

unfold
let impl__get
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Ops.Index.t_Index (t_Slice v_T) v_I)
     = impl__get' #v_T #v_I #i0

let impl__copy_from_slice
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (s src: t_Slice v_T)
    : Prims.Pure (t_Slice v_T)
      (requires (impl__len #v_T s <: usize) =. (impl__len #v_T src <: usize))
      (fun _ -> Prims.l_True) =
  let s:t_Slice v_T = Rust_primitives.Mem.replace #(t_Slice v_T) s src in
  s

let impl__clone_from_slice
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (s src: t_Slice v_T)
    : Prims.Pure (t_Slice v_T)
      (requires (impl__len #v_T s <: usize) =. (impl__len #v_T src <: usize))
      (fun _ -> Prims.l_True) =
  let s:t_Slice v_T = Rust_primitives.Mem.replace #(t_Slice v_T) s src in
  s

let impl__split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize)
    : Prims.Pure (t_Slice v_T & t_Slice v_T)
      (requires mid <=. (impl__len #v_T s <: usize))
      (fun _ -> Prims.l_True) = Rust_primitives.Slice.slice_split_at #v_T s mid

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Slice v_T) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (self_: t_Slice v_T) (i: usize) -> i <. (impl__len #v_T self_ <: usize));
    f_index_post = (fun (self: t_Slice v_T) (i: usize) (out: v_T) -> true);
    f_index = fun (self: t_Slice v_T) (i: usize) -> Rust_primitives.Slice.slice_index #v_T self i
  }
