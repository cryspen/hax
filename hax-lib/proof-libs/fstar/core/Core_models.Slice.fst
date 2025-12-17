module Core_models.Slice
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

let impl__len (#v_T: Type0) (s: t_Slice v_T) : usize = Rust_primitives.Slice.slice_length #v_T s

let impl__chunks (#v_T: Type0) (s: t_Slice v_T) (cs: usize) : Core_models.Slice.Iter.t_Chunks v_T =
  Core_models.Slice.Iter.impl__new #v_T cs s

let impl__iter (#v_T: Type0) (s: t_Slice v_T) : Core_models.Slice.Iter.t_Iter v_T =
  Core_models.Slice.Iter.Iter (Rust_primitives.Sequence.seq_from_slice #v_T s)
  <:
  Core_models.Slice.Iter.t_Iter v_T

let impl__chunks_exact (#v_T: Type0) (s: t_Slice v_T) (cs: usize)
    : Core_models.Slice.Iter.t_ChunksExact v_T = Core_models.Slice.Iter.impl_1__new #v_T cs s

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
let impl_6 (#v_T: Type0)
    : Core_models.Ops.Index.t_Index (t_Slice v_T) (Core_models.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: Core_models.Ops.Range.t_Range usize) ->
        i.Core_models.Ops.Range.f_start <=. i.Core_models.Ops.Range.f_end &&
        i.Core_models.Ops.Range.f_end <=. (impl__len #v_T self_ <: usize));
    f_index_post
    =
    (fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_Range usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_Range usize) ->
      Rust_primitives.Slice.slice_slice #v_T
        self
        i.Core_models.Ops.Range.f_start
        i.Core_models.Ops.Range.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (#v_T: Type0)
    : Core_models.Ops.Index.t_Index (t_Slice v_T) (Core_models.Ops.Range.t_RangeTo usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeTo usize) ->
        i.Core_models.Ops.Range.f_end <=. (impl__len #v_T self_ <: usize));
    f_index_post
    =
    (fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeTo usize) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeTo usize) ->
      Rust_primitives.Slice.slice_slice #v_T self (mk_usize 0) i.Core_models.Ops.Range.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (#v_T: Type0)
    : Core_models.Ops.Index.t_Index (t_Slice v_T) (Core_models.Ops.Range.t_RangeFrom usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeFrom usize) ->
        i.Core_models.Ops.Range.f_start <=. (impl__len #v_T self_ <: usize));
    f_index_post
    =
    (fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeFrom usize) (out: t_Slice v_T) -> true
    );
    f_index
    =
    fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeFrom usize) ->
      Rust_primitives.Slice.slice_slice #v_T
        self
        i.Core_models.Ops.Range.f_start
        (Rust_primitives.Slice.slice_length #v_T self <: usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (#v_T: Type0)
    : Core_models.Ops.Index.t_Index (t_Slice v_T) Core_models.Ops.Range.t_RangeFull =
  {
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeFull) -> true);
    f_index_post
    =
    (fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeFull) (out: t_Slice v_T) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: Core_models.Ops.Range.t_RangeFull) ->
      Rust_primitives.Slice.slice_slice #v_T
        self
        (mk_usize 0)
        (Rust_primitives.Slice.slice_length #v_T self <: usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (#v_T: Type0) : Core_models.Ops.Index.t_Index (t_Slice v_T) usize =
  {
    f_Output = v_T;
    f_index_pre = (fun (self_: t_Slice v_T) (i: usize) -> i <. (impl__len #v_T self_ <: usize));
    f_index_post = (fun (self: t_Slice v_T) (i: usize) (out: v_T) -> true);
    f_index = fun (self: t_Slice v_T) (i: usize) -> Rust_primitives.Slice.slice_index #v_T self i
  }

class t_SliceIndex (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_get_pre:self_: v_Self -> slice: v_T -> pred: Type0{true ==> pred};
  f_get_post:v_Self -> v_T -> Core_models.Option.t_Option f_Output -> Type0;
  f_get:x0: v_Self -> x1: v_T
    -> Prims.Pure (Core_models.Option.t_Option f_Output)
        (f_get_pre x0 x1)
        (fun result -> f_get_post x0 x1 result)
}

let impl__get
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_SliceIndex v_I (t_Slice v_T))
      (s: t_Slice v_T)
      (index: v_I)
    : Core_models.Option.t_Option i0.f_Output =
  f_get #v_I #(t_Slice v_T) #FStar.Tactics.Typeclasses.solve index s

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : t_SliceIndex usize (t_Slice v_T) =
  {
    f_Output = v_T;
    f_get_pre = (fun (self: usize) (slice: t_Slice v_T) -> true);
    f_get_post
    =
    (fun (self: usize) (slice: t_Slice v_T) (out: Core_models.Option.t_Option v_T) -> true);
    f_get
    =
    fun (self: usize) (slice: t_Slice v_T) ->
      if self <. (impl__len #v_T slice <: usize)
      then
        Core_models.Option.Option_Some (Rust_primitives.Slice.slice_index #v_T slice self)
        <:
        Core_models.Option.t_Option v_T
      else Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : t_SliceIndex Core_models.Ops.Range.t_RangeFull (t_Slice v_T) =
  {
    f_Output = t_Slice v_T;
    f_get_pre = (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> true);
    f_get_post
    =
    (fun
        (self: Core_models.Ops.Range.t_RangeFull)
        (slice: t_Slice v_T)
        (out: Core_models.Option.t_Option (t_Slice v_T))
        ->
        true);
    f_get
    =
    fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) ->
      Core_models.Option.Option_Some slice <: Core_models.Option.t_Option (t_Slice v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : t_SliceIndex (Core_models.Ops.Range.t_RangeFrom usize) (t_Slice v_T) =
  {
    f_Output = t_Slice v_T;
    f_get_pre = (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) -> true);
    f_get_post
    =
    (fun
        (self: Core_models.Ops.Range.t_RangeFrom usize)
        (slice: t_Slice v_T)
        (out: Core_models.Option.t_Option (t_Slice v_T))
        ->
        true);
    f_get
    =
    fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
      if self.Core_models.Ops.Range.f_start <. (impl__len #v_T slice <: usize)
      then
        Core_models.Option.Option_Some
        (Rust_primitives.Slice.slice_slice #v_T
            slice
            self.Core_models.Ops.Range.f_start
            (impl__len #v_T slice <: usize))
        <:
        Core_models.Option.t_Option (t_Slice v_T)
      else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : t_SliceIndex (Core_models.Ops.Range.t_RangeTo usize) (t_Slice v_T) =
  {
    f_Output = t_Slice v_T;
    f_get_pre = (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) -> true);
    f_get_post
    =
    (fun
        (self: Core_models.Ops.Range.t_RangeTo usize)
        (slice: t_Slice v_T)
        (out: Core_models.Option.t_Option (t_Slice v_T))
        ->
        true);
    f_get
    =
    fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) ->
      if self.Core_models.Ops.Range.f_end <=. (impl__len #v_T slice <: usize)
      then
        Core_models.Option.Option_Some
        (Rust_primitives.Slice.slice_slice #v_T slice (mk_usize 0) self.Core_models.Ops.Range.f_end)
        <:
        Core_models.Option.t_Option (t_Slice v_T)
      else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) : t_SliceIndex (Core_models.Ops.Range.t_Range usize) (t_Slice v_T) =
  {
    f_Output = t_Slice v_T;
    f_get_pre = (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) -> true);
    f_get_post
    =
    (fun
        (self: Core_models.Ops.Range.t_Range usize)
        (slice: t_Slice v_T)
        (out: Core_models.Option.t_Option (t_Slice v_T))
        ->
        true);
    f_get
    =
    fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) ->
      if
        self.Core_models.Ops.Range.f_start <. self.Core_models.Ops.Range.f_end &&
        self.Core_models.Ops.Range.f_end <=. (impl__len #v_T slice <: usize)
      then
        Core_models.Option.Option_Some
        (Rust_primitives.Slice.slice_slice #v_T
            slice
            self.Core_models.Ops.Range.f_start
            self.Core_models.Ops.Range.f_end)
        <:
        Core_models.Option.t_Option (t_Slice v_T)
      else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T)
  }
