module Core_models.Slice
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::slice::len`]
let impl__len (#v_T: Type0) (s: t_Slice v_T) : usize = Rust_primitives.Slice.slice_length #v_T s

/// See [`std::slice::iter`]
let impl__iter (#v_T: Type0) (s: t_Slice v_T) : Core_models.Slice.Iter.t_Iter v_T =
  Core_models.Slice.Iter.Iter (Rust_primitives.Sequence.seq_from_slice #v_T s)
  <:
  Core_models.Slice.Iter.t_Iter v_T

/// See [`std::slice::is_empty`]
let impl__is_empty (#v_T: Type0) (s: t_Slice v_T) : bool = (impl__len #v_T s <: usize) =. mk_usize 0

/// See [`std::slice::contains`]
assume
val impl__contains':
    #v_T: Type0 ->
    {| i0: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    s: t_Slice v_T ->
    v: v_T
  -> bool

unfold
let impl__contains
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_T)
     = impl__contains' #v_T #i0

/// See [`std::slice::copy_within`]
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

/// See [`std::slice::binary_search`]
assume
val impl__binary_search':
    #v_T: Type0 ->
    {| i0: Core_models.Cmp.t_Ord v_T |} ->
    s: t_Slice v_T ->
    x: v_T
  -> Core_models.Result.t_Result usize usize

unfold
let impl__binary_search
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
     = impl__binary_search' #v_T #i0

/// See [`std::slice::get`]
let impl__get
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Slice.Index.t_SliceIndex v_I (t_Slice v_T))
      (s: t_Slice v_T)
      (index: v_I)
    : Core_models.Option.t_Option i0.f_Output =
  Core_models.Slice.Index.f_get #v_I #(t_Slice v_T) #FStar.Tactics.Typeclasses.solve index s

/// See [`std::slice::first`]
let impl__first (#v_T: Type0) (s: t_Slice v_T) : Core_models.Option.t_Option v_T =
  if impl__is_empty #v_T s
  then Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  else
    Core_models.Option.Option_Some (Rust_primitives.Slice.slice_index #v_T s (mk_usize 0))
    <:
    Core_models.Option.t_Option v_T

/// See [`std::slice::last`]
let impl__last (#v_T: Type0) (s: t_Slice v_T) : Core_models.Option.t_Option v_T =
  if impl__is_empty #v_T s
  then Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  else
    Core_models.Option.Option_Some
    (Rust_primitives.Slice.slice_index #v_T s ((impl__len #v_T s <: usize) -! mk_usize 1 <: usize))
    <:
    Core_models.Option.t_Option v_T

/// See [`std::slice::reverse`]
assume
val impl__reverse': #v_T: Type0 -> s: t_Slice v_T -> t_Slice v_T

unfold
let impl__reverse (#v_T: Type0) = impl__reverse' #v_T

/// See [`std::slice::fill`]
assume
val impl__fill':
    #v_T: Type0 ->
    {| i0: Core_models.Clone.t_Clone v_T |} ->
    s: t_Slice v_T ->
    value: v_T
  -> t_Slice v_T

unfold
let impl__fill
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
     = impl__fill' #v_T #i0

/// See [`std::slice::fill_with`]
assume
val impl__fill_with':
    #v_T: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F Prims.unit |} ->
    s: t_Slice v_T ->
    f: v_F
  -> t_Slice v_T

unfold
let impl__fill_with
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F Prims.unit)
     = impl__fill_with' #v_T #v_F #i0

/// See [`std::slice::as_slice`]
let impl__as_slice (#v_T: Type0) (s: t_Slice v_T) : t_Slice v_T = s

/// See [`std::slice::split_first`]
let impl__split_first (#v_T: Type0) (s: t_Slice v_T)
    : Core_models.Option.t_Option (v_T & t_Slice v_T) =
  if impl__is_empty #v_T s
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (v_T & t_Slice v_T)
  else
    Core_models.Option.Option_Some
    (Rust_primitives.Slice.slice_index #v_T s (mk_usize 0),
      Rust_primitives.Slice.slice_slice #v_T s (mk_usize 1) (impl__len #v_T s <: usize)
      <:
      (v_T & t_Slice v_T))
    <:
    Core_models.Option.t_Option (v_T & t_Slice v_T)

/// See [`std::slice::split_last`]
let impl__split_last (#v_T: Type0) (s: t_Slice v_T)
    : Core_models.Option.t_Option (v_T & t_Slice v_T) =
  if impl__is_empty #v_T s
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (v_T & t_Slice v_T)
  else
    let l:usize = impl__len #v_T s in
    Core_models.Option.Option_Some
    (Rust_primitives.Slice.slice_index #v_T s (l -! mk_usize 1 <: usize),
      Rust_primitives.Slice.slice_slice #v_T s (mk_usize 0) (l -! mk_usize 1 <: usize)
      <:
      (v_T & t_Slice v_T))
    <:
    Core_models.Option.t_Option (v_T & t_Slice v_T)

/// See [`std::slice::split`]
let impl__split
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (pred: v_P)
    : Core_models.Slice.Iter.t_Split v_T v_P = Core_models.Slice.Iter.impl_11__new #v_T #v_P s pred

/// See [`std::slice::split_inclusive`]
let impl__split_inclusive
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (pred: v_P)
    : Core_models.Slice.Iter.t_SplitInclusive v_T v_P =
  Core_models.Slice.Iter.impl_13__new #v_T #v_P s pred

/// See [`std::slice::splitn`]
let impl__splitn
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (n: usize)
      (pred: v_P)
    : Core_models.Slice.Iter.t_SplitN v_T v_P =
  Core_models.Slice.Iter.impl_15__new #v_T #v_P s n pred

/// See [`std::slice::rsplit`]
let impl__rsplit
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (pred: v_P)
    : Core_models.Slice.Iter.t_RSplit v_T v_P = Core_models.Slice.Iter.impl_17__new #v_T #v_P s pred

/// See [`std::slice::rsplitn`]
let impl__rsplitn
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (n: usize)
      (pred: v_P)
    : Core_models.Slice.Iter.t_RSplitN v_T v_P =
  Core_models.Slice.Iter.impl_19__new #v_T #v_P s n pred

/// See [`std::slice::chunk_by`]
let impl__chunk_by
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P (v_T & v_T))
      (s: t_Slice v_T)
      (pred: v_P)
    : Core_models.Slice.Iter.t_ChunkBy v_T v_P =
  Core_models.Slice.Iter.impl_21__new #v_T #v_P s pred

/// See [`std::slice::split_once`]
let impl__split_once
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (pred: v_P)
    : Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T) =
  let len:usize = impl__len #v_T s in
  let idx:usize = Core_models.Slice.Iter.position_of #v_T #v_P s pred in
  if idx =. len
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T)
  else
    Core_models.Option.Option_Some
    (Rust_primitives.Slice.slice_slice #v_T s (mk_usize 0) idx,
      Rust_primitives.Slice.slice_slice #v_T s (idx +! mk_usize 1 <: usize) len
      <:
      (t_Slice v_T & t_Slice v_T))
    <:
    Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T)

/// See [`std::slice::rsplit_once`]
let impl__rsplit_once
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
      (s: t_Slice v_T)
      (pred: v_P)
    : Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T) =
  let len:usize = impl__len #v_T s in
  let idx:usize = Core_models.Slice.Iter.rposition_of #v_T #v_P s pred in
  if idx =. len
  then Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T)
  else
    Core_models.Option.Option_Some
    (Rust_primitives.Slice.slice_slice #v_T s (mk_usize 0) idx,
      Rust_primitives.Slice.slice_slice #v_T s (idx +! mk_usize 1 <: usize) len
      <:
      (t_Slice v_T & t_Slice v_T))
    <:
    Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T)

/// See [`std::slice::binary_search_by`]
assume
val impl__binary_search_by':
    #v_T: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F v_T |} ->
    s: t_Slice v_T ->
    f: v_F
  -> Core_models.Result.t_Result usize usize

unfold
let impl__binary_search_by
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl__binary_search_by' #v_T #v_F #i0

/// See [`std::slice::binary_search_by_key`]
assume
val impl__binary_search_by_key':
    #v_T: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Cmp.t_Ord v_B |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F v_T |} ->
    s: t_Slice v_T ->
    b: v_B ->
    f: v_F
  -> Core_models.Result.t_Result usize usize

unfold
let impl__binary_search_by_key
      (#v_T #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl__binary_search_by_key' #v_T #v_B #v_F #i0 #i1

/// See [`std::slice::partition_point`]
assume
val impl__partition_point':
    #v_T: Type0 ->
    #v_P: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_P v_T |} ->
    s: t_Slice v_T ->
    pred: v_P
  -> usize

unfold
let impl__partition_point
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
     = impl__partition_point' #v_T #v_P #i0

/// See [`std::slice::is_sorted`]
assume
val impl__is_sorted':
    #v_T: Type0 ->
    {| i0: Core_models.Cmp.t_PartialOrd v_T v_T |} ->
    s: t_Slice v_T
  -> bool

unfold
let impl__is_sorted
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialOrd v_T v_T)
     = impl__is_sorted' #v_T #i0

/// See [`std::slice::is_sorted_by`]
assume
val impl__is_sorted_by':
    #v_T: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F (v_T & v_T) |} ->
    s: t_Slice v_T ->
    compare: v_F
  -> bool

unfold
let impl__is_sorted_by
      (#v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F (v_T & v_T))
     = impl__is_sorted_by' #v_T #v_F #i0

/// See [`std::slice::is_sorted_by_key`]
assume
val impl__is_sorted_by_key':
    #v_T: Type0 ->
    #v_K: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Cmp.t_PartialOrd v_K v_K |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F v_T |} ->
    s: t_Slice v_T ->
    f: v_F
  -> bool

unfold
let impl__is_sorted_by_key
      (#v_T #v_K #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialOrd v_K v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl__is_sorted_by_key' #v_T #v_K #v_F #i0 #i1

/// See [`std::slice::starts_with`]
assume
val impl__starts_with':
    #v_T: Type0 ->
    {| i0: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    s: t_Slice v_T ->
    needle: t_Slice v_T
  -> bool

unfold
let impl__starts_with
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_T)
     = impl__starts_with' #v_T #i0

/// See [`std::slice::ends_with`]
assume
val impl__ends_with':
    #v_T: Type0 ->
    {| i0: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    s: t_Slice v_T ->
    needle: t_Slice v_T
  -> bool

unfold
let impl__ends_with
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_T)
     = impl__ends_with' #v_T #i0

/// See [`std::slice::chunks`]
let impl__chunks (#v_T: Type0) (s: t_Slice v_T) (cs: usize)
    : Prims.Pure (Core_models.Slice.Iter.t_Chunks v_T)
      (requires cs >. mk_usize 0)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit = if cs =. mk_usize 0 then Core_models.Panicking.Internal.panic #Prims.unit () in
  Core_models.Slice.Iter.impl__new #v_T cs s

/// See [`std::slice::chunks_exact`]
let impl__chunks_exact (#v_T: Type0) (s: t_Slice v_T) (cs: usize)
    : Prims.Pure (Core_models.Slice.Iter.t_ChunksExact v_T)
      (requires cs >. mk_usize 0)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit = if cs =. mk_usize 0 then Core_models.Panicking.Internal.panic #Prims.unit () in
  Core_models.Slice.Iter.impl_1__new #v_T cs s

/// See [`std::slice::copy_from_slice`]
let impl__copy_from_slice
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Marker.t_Copy v_T)
      (s src: t_Slice v_T)
    : Prims.Pure (t_Slice v_T)
      (requires (impl__len #v_T s <: usize) =. (impl__len #v_T src <: usize))
      (fun _ -> Prims.l_True) =
  let s:t_Slice v_T = Rust_primitives.Slice.slice_clone_from_slice #v_T s src in
  s

/// See [`std::slice::clone_from_slice`]
let impl__clone_from_slice
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (s src: t_Slice v_T)
    : Prims.Pure (t_Slice v_T)
      (requires (impl__len #v_T s <: usize) =. (impl__len #v_T src <: usize))
      (fun _ -> Prims.l_True) =
  let s:t_Slice v_T = Rust_primitives.Slice.slice_clone_from_slice #v_T s src in
  s

/// See [`std::slice::split_at`]
let impl__split_at (#v_T: Type0) (s: t_Slice v_T) (mid: usize)
    : Prims.Pure (t_Slice v_T & t_Slice v_T)
      (requires mid <=. (impl__len #v_T s <: usize))
      (fun _ -> Prims.l_True) = Rust_primitives.Slice.slice_split_at #v_T s mid

/// See [`std::slice::split_at_checked`]
let impl__split_at_checked (#v_T: Type0) (s: t_Slice v_T) (mid: usize)
    : Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T) =
  if mid <=. (impl__len #v_T s <: usize)
  then
    Core_models.Option.Option_Some (impl__split_at #v_T s mid)
    <:
    Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T)
  else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T & t_Slice v_T)

/// See [`std::slice::get_unchecked`]
assume
val impl__get_unchecked':
    #v_T: Type0 ->
    #v_I: Type0 ->
    {| i0: Core_models.Slice.Index.t_SliceIndex v_I (t_Slice v_T) |} ->
    s: t_Slice v_T ->
    index: v_I
  -> Prims.Pure i0.f_Output
      (requires
        Core_models.Option.impl__is_some #i0.f_Output
          (Core_models.Slice.Index.f_get #v_I
              #(t_Slice v_T)
              #FStar.Tactics.Typeclasses.solve
              index
              s
            <:
            Core_models.Option.t_Option i0.f_Output))
      (fun _ -> Prims.l_True)

unfold
let impl__get_unchecked
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Slice.Index.t_SliceIndex v_I (t_Slice v_T))
     = impl__get_unchecked' #v_T #v_I #i0

/// See [`std::slice::swap`]
assume
val impl__swap': #v_T: Type0 -> s: t_Slice v_T -> a: usize -> b: usize
  -> Prims.Pure (t_Slice v_T)
      (requires a <. (impl__len #v_T s <: usize) && b <. (impl__len #v_T s <: usize))
      (fun _ -> Prims.l_True)

unfold
let impl__swap (#v_T: Type0) = impl__swap' #v_T

/// See [`std::slice::windows`]
let impl__windows (#v_T: Type0) (s: t_Slice v_T) (size: usize)
    : Prims.Pure (Core_models.Slice.Iter.t_Windows v_T)
      (requires size >. mk_usize 0)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if size =. mk_usize 0 then Core_models.Panicking.Internal.panic #Prims.unit ()
  in
  Core_models.Slice.Iter.impl_5__new #v_T size s

/// See [`std::slice::split_at_unchecked`]
let impl__split_at_unchecked (#v_T: Type0) (s: t_Slice v_T) (mid: usize)
    : Prims.Pure (t_Slice v_T & t_Slice v_T)
      (requires mid <=. (impl__len #v_T s <: usize))
      (fun _ -> Prims.l_True) = Rust_primitives.Slice.slice_split_at #v_T s mid

/// See [`std::slice::swap_unchecked`]
assume
val impl__swap_unchecked': #v_T: Type0 -> s: t_Slice v_T -> a: usize -> b: usize
  -> Prims.Pure (t_Slice v_T)
      (requires a <. (impl__len #v_T s <: usize) && b <. (impl__len #v_T s <: usize))
      (fun _ -> Prims.l_True)

unfold
let impl__swap_unchecked (#v_T: Type0) = impl__swap_unchecked' #v_T

/// See [`std::slice::rotate_left`]
assume
val impl__rotate_left': #v_T: Type0 -> s: t_Slice v_T -> mid: usize
  -> Prims.Pure (t_Slice v_T) (requires mid <=. (impl__len #v_T s <: usize)) (fun _ -> Prims.l_True)

unfold
let impl__rotate_left (#v_T: Type0) = impl__rotate_left' #v_T

/// See [`std::slice::rotate_right`]
assume
val impl__rotate_right': #v_T: Type0 -> s: t_Slice v_T -> k: usize
  -> Prims.Pure (t_Slice v_T) (requires k <=. (impl__len #v_T s <: usize)) (fun _ -> Prims.l_True)

unfold
let impl__rotate_right (#v_T: Type0) = impl__rotate_right' #v_T

/// See [`std::slice::rchunks`]
let impl__rchunks (#v_T: Type0) (s: t_Slice v_T) (cs: usize)
    : Prims.Pure (Core_models.Slice.Iter.t_RChunks v_T)
      (requires cs >. mk_usize 0)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit = if cs =. mk_usize 0 then Core_models.Panicking.Internal.panic #Prims.unit () in
  Core_models.Slice.Iter.impl_7__new #v_T cs s

/// See [`std::slice::rchunks_exact`]
let impl__rchunks_exact (#v_T: Type0) (s: t_Slice v_T) (cs: usize)
    : Prims.Pure (Core_models.Slice.Iter.t_RChunksExact v_T)
      (requires cs >. mk_usize 0)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit = if cs =. mk_usize 0 then Core_models.Panicking.Internal.panic #Prims.unit () in
  Core_models.Slice.Iter.impl_9__new #v_T cs s

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': #v_U: Type0 -> #v_T: Type0 -> {| i0: Core_models.Cmp.t_PartialEq v_T v_U |}
  -> Core_models.Cmp.t_PartialEq (t_Slice v_T) (t_Slice v_U)

unfold
let impl_1
      (#v_U #v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_U)
     = impl_1' #v_U #v_T #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Eq v_T)
    : Core_models.Cmp.t_Eq (t_Slice v_T) = { _super_i0 = FStar.Tactics.Typeclasses.solve }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': #v_T: Type0 -> {| i0: Core_models.Cmp.t_PartialOrd v_T v_T |}
  -> Core_models.Cmp.t_PartialOrd (t_Slice v_T) (t_Slice v_T)

unfold
let impl_3
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialOrd v_T v_T)
     = impl_3' #v_T #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': #v_T: Type0 -> {| i0: Core_models.Cmp.t_Ord v_T |}
  -> Core_models.Cmp.t_Ord (t_Slice v_T)

unfold
let impl_4 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T) =
  impl_4' #v_T #i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_T: Type0) : Core_models.Iter.Traits.Collect.t_IntoIterator (t_Slice v_T) =
  {
    f_Item = v_T;
    f_IntoIter = Core_models.Slice.Iter.t_Iter v_T;
    f_into_iter_pre = (fun (self: t_Slice v_T) -> true);
    f_into_iter_post = (fun (self: t_Slice v_T) (out: Core_models.Slice.Iter.t_Iter v_T) -> true);
    f_into_iter = fun (self: t_Slice v_T) -> impl__iter #v_T self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_T: Type0)
    : Core_models.Ops.Index.t_Index (t_Slice v_T) (Core_models.Ops.Range.t_Range usize) =
  {
    f_Output = t_Slice v_T;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: Core_models.Ops.Range.t_Range usize) ->
        i.Core_models.Ops.Range.f_start <=. i.Core_models.Ops.Range.f_end &&
        i.Core_models.Ops.Range.f_end <=. (Rust_primitives.Slice.slice_length #v_T self_ <: usize));
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
        i.Core_models.Ops.Range.f_end <=. (Rust_primitives.Slice.slice_length #v_T self_ <: usize));
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
        i.Core_models.Ops.Range.f_start <=. (Rust_primitives.Slice.slice_length #v_T self_ <: usize)
    );
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
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: usize) ->
        i <. (Rust_primitives.Slice.slice_length #v_T self_ <: usize));
    f_index_post = (fun (self: t_Slice v_T) (i: usize) (out: v_T) -> true);
    f_index = fun (self: t_Slice v_T) (i: usize) -> Rust_primitives.Slice.slice_index #v_T self i
  }

/// See [`std::slice::SlicePattern`]
class t_SlicePattern (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Item:Type0;
  f_as_slice_pre:v_Self -> Type0;
  f_as_slice_post:v_Self -> t_Slice f_Item -> Type0;
  f_as_slice:x0: v_Self
    -> Prims.Pure (t_Slice f_Item) (f_as_slice_pre x0) (fun result -> f_as_slice_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11 (#v_T: Type0) : t_SlicePattern (t_Slice v_T) =
  {
    f_Item = v_T;
    f_as_slice_pre = (fun (self: t_Slice v_T) -> true);
    f_as_slice_post = (fun (self: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_as_slice = fun (self: t_Slice v_T) -> self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12 (#v_T: Type0) (v_N: usize) : t_SlicePattern (t_Array v_T v_N) =
  {
    f_Item = v_T;
    f_as_slice_pre = (fun (self: t_Array v_T v_N) -> true);
    f_as_slice_post = (fun (self: t_Array v_T v_N) (out: t_Slice v_T) -> true);
    f_as_slice = fun (self: t_Array v_T v_N) -> Rust_primitives.Slice.array_as_slice #v_T v_N self
  }

/// See [`std::slice::strip_prefix`]
assume
val impl_13__strip_prefix':
    #v_T: Type0 ->
    #v_P: Type0 ->
    {| i0: t_SlicePattern v_P |} ->
    {| i1: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    #_: unit{i0.f_Item == v_T} ->
    s: t_Slice v_T ->
    prefix: v_P
  -> Core_models.Option.t_Option (t_Slice v_T)

unfold
let impl_13__strip_prefix
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_SlicePattern v_P)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_PartialEq v_T v_T)
      (#_: unit{i0.f_Item == v_T})
     = impl_13__strip_prefix' #v_T #v_P #i0 #i1 #_

/// See [`std::slice::strip_suffix`]
assume
val impl_13__strip_suffix':
    #v_T: Type0 ->
    #v_P: Type0 ->
    {| i0: t_SlicePattern v_P |} ->
    {| i1: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    #_: unit{i0.f_Item == v_T} ->
    s: t_Slice v_T ->
    suffix: v_P
  -> Core_models.Option.t_Option (t_Slice v_T)

unfold
let impl_13__strip_suffix
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_SlicePattern v_P)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_PartialEq v_T v_T)
      (#_: unit{i0.f_Item == v_T})
     = impl_13__strip_suffix' #v_T #v_P #i0 #i1 #_

/// See [`std::slice::trim_prefix`]
let impl_13__trim_prefix
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_SlicePattern v_P)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_PartialEq v_T v_T)
      (#_: unit{i0.f_Item == v_T})
      (s: t_Slice v_T)
      (prefix: v_P)
    : t_Slice v_T =
  match impl_13__strip_prefix #v_T #v_P s prefix <: Core_models.Option.t_Option (t_Slice v_T) with
  | Core_models.Option.Option_Some rest -> rest
  | Core_models.Option.Option_None  -> s

/// See [`std::slice::trim_suffix`]
let impl_13__trim_suffix
      (#v_T #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_SlicePattern v_P)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_PartialEq v_T v_T)
      (#_: unit{i0.f_Item == v_T})
      (s: t_Slice v_T)
      (suffix: v_P)
    : t_Slice v_T =
  match impl_13__strip_suffix #v_T #v_P s suffix <: Core_models.Option.t_Option (t_Slice v_T) with
  | Core_models.Option.Option_Some rest -> rest
  | Core_models.Option.Option_None  -> s

/// See [`std::slice::strip_circumfix`]
let impl_13__strip_circumfix
      (#v_T #v_S #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_SlicePattern v_S)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_SlicePattern v_P)
      (#_: unit{i1.f_Item == v_T})
      (#_: unit{i2.f_Item == v_T})
      (s: t_Slice v_T)
      (prefix: v_P)
      (suffix: v_S)
    : Core_models.Option.t_Option (t_Slice v_T) =
  match impl_13__strip_prefix #v_T #v_P s prefix <: Core_models.Option.t_Option (t_Slice v_T) with
  | Core_models.Option.Option_Some rest -> impl_13__strip_suffix #v_T #v_S rest suffix
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T)
