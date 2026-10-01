module Core_models.Slice.Index
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

let start_index
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Range.t_RangeBounds v_R usize)
      (range: v_R)
    : Core_models.Option.t_Option usize =
  match
    Core_models.Ops.Range.f_start_bound #v_R #usize #FStar.Tactics.Typeclasses.solve range
    <:
    Core_models.Ops.Range.t_Bound usize
  with
  | Core_models.Ops.Range.Bound_Included start ->
    Core_models.Option.Option_Some start <: Core_models.Option.t_Option usize
  | Core_models.Ops.Range.Bound_Excluded start ->
    Core_models.Num.impl_usize__checked_add start (mk_usize 1)
  | Core_models.Ops.Range.Bound_Unbounded  ->
    Core_models.Option.Option_Some (mk_usize 0) <: Core_models.Option.t_Option usize

let end_index
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Range.t_RangeBounds v_R usize)
      (range: v_R)
      (len: usize)
    : Core_models.Option.t_Option usize =
  match
    Core_models.Ops.Range.f_end_bound #v_R #usize #FStar.Tactics.Typeclasses.solve range
    <:
    Core_models.Ops.Range.t_Bound usize
  with
  | Core_models.Ops.Range.Bound_Included v_end ->
    Core_models.Num.impl_usize__checked_add v_end (mk_usize 1)
  | Core_models.Ops.Range.Bound_Excluded v_end ->
    Core_models.Option.Option_Some v_end <: Core_models.Option.t_Option usize
  | Core_models.Ops.Range.Bound_Unbounded  ->
    Core_models.Option.Option_Some len <: Core_models.Option.t_Option usize

/// See [`std::slice::try_range`]
let try_range
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Range.t_RangeBounds v_R usize)
      (range: v_R)
      (bounds: Core_models.Ops.Range.t_RangeTo usize)
    : Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize) =
  let len:usize = bounds.Core_models.Ops.Range.f_end in
  match start_index #v_R range <: Core_models.Option.t_Option usize with
  | Core_models.Option.Option_Some start ->
    (match end_index #v_R range len <: Core_models.Option.t_Option usize with
      | Core_models.Option.Option_Some v_end ->
        if start >. v_end || v_end >. len
        then
          Core_models.Option.Option_None
          <:
          Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize)
        else
          Core_models.Option.Option_Some
          ({ Core_models.Ops.Range.f_start = start; Core_models.Ops.Range.f_end = v_end }
            <:
            Core_models.Ops.Range.t_Range usize)
          <:
          Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize)
      | Core_models.Option.Option_None  ->
        Core_models.Option.Option_None
        <:
        Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize))
  | Core_models.Option.Option_None  ->
    Core_models.Option.Option_None
    <:
    Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize)

/// See [`std::slice::range`]
let range
      (#v_R: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Range.t_RangeBounds v_R usize)
      (range: v_R)
      (bounds: Core_models.Ops.Range.t_RangeTo usize)
    : Prims.Pure (Core_models.Ops.Range.t_Range usize)
      (requires
        Core_models.Option.impl__is_some #(Core_models.Ops.Range.t_Range usize)
          (try_range #v_R range bounds
            <:
            Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize)))
      (fun _ -> Prims.l_True) =
  match
    try_range #v_R range bounds <: Core_models.Option.t_Option (Core_models.Ops.Range.t_Range usize)
  with
  | Core_models.Option.Option_Some r -> r
  | Core_models.Option.Option_None  ->
    Core_models.Panicking.Internal.panic #(Core_models.Ops.Range.t_Range usize) ()

/// See [`std::slice::SliceIndex`]. `get_unchecked` is the same in-bounds
/// projection as `index` (no raw pointers); the `*_mut` variants take
/// `&mut T` and return `&mut Output`.
class t_SliceIndex (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_get_pre:self_: v_Self -> slice: v_T -> pred: Type0{true ==> pred};
  f_get_post:v_Self -> v_T -> Core_models.Option.t_Option f_Output -> Type0;
  f_get:x0: v_Self -> x1: v_T
    -> Prims.Pure (Core_models.Option.t_Option f_Output)
        (f_get_pre x0 x1)
        (fun result -> f_get_post x0 x1 result);
  f_index_pre:v_Self -> v_T -> Type0;
  f_index_post:v_Self -> v_T -> f_Output -> Type0;
  f_index:x0: v_Self -> x1: v_T
    -> Prims.Pure f_Output (f_index_pre x0 x1) (fun result -> f_index_post x0 x1 result);
  f_get_unchecked_pre:v_Self -> v_T -> Type0;
  f_get_unchecked_post:v_Self -> v_T -> f_Output -> Type0;
  f_get_unchecked:x0: v_Self -> x1: v_T
    -> Prims.Pure f_Output
        (f_get_unchecked_pre x0 x1)
        (fun result -> f_get_unchecked_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_SliceIndex usize (t_Slice v_T) =
  {
    f_Output = v_T;
    f_get_pre = (fun (self: usize) (slice: t_Slice v_T) -> true);
    f_get_post
    =
    (fun (self: usize) (slice: t_Slice v_T) (out: Core_models.Option.t_Option v_T) -> true);
    f_get
    =
    (fun (self: usize) (slice: t_Slice v_T) ->
        if self <. (Rust_primitives.Slice.slice_length #v_T slice <: usize)
        then
          Core_models.Option.Option_Some (Rust_primitives.Slice.slice_index #v_T slice self)
          <:
          Core_models.Option.t_Option v_T
        else Core_models.Option.Option_None <: Core_models.Option.t_Option v_T);
    f_index_pre
    =
    (fun (self_: usize) (slice: t_Slice v_T) ->
        self_ <. (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_index_post = (fun (self: usize) (slice: t_Slice v_T) (out: v_T) -> true);
    f_index
    =
    (fun (self: usize) (slice: t_Slice v_T) -> Rust_primitives.Slice.slice_index #v_T slice self);
    f_get_unchecked_pre
    =
    (fun (self_: usize) (slice: t_Slice v_T) ->
        self_ <. (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_get_unchecked_post = (fun (self: usize) (slice: t_Slice v_T) (out: v_T) -> true);
    f_get_unchecked
    =
    fun (self: usize) (slice: t_Slice v_T) -> Rust_primitives.Slice.slice_index #v_T slice self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) : t_SliceIndex Core_models.Ops.Range.t_RangeFull (t_Slice v_T) =
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
    (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) ->
        Core_models.Option.Option_Some slice <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre = (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> true);
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_index = (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> slice);
    f_get_unchecked_pre
    =
    (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> true);
    f_get_unchecked_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_get_unchecked = fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> slice
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : t_SliceIndex (Core_models.Ops.Range.t_RangeFrom usize) (t_Slice v_T) =
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
    (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
        if
          self.Core_models.Ops.Range.f_start <=.
          (Rust_primitives.Slice.slice_length #v_T slice <: usize)
        then
          Core_models.Option.Option_Some
          (Rust_primitives.Slice.slice_slice #v_T
              slice
              self.Core_models.Ops.Range.f_start
              (Rust_primitives.Slice.slice_length #v_T slice <: usize))
          <:
          Core_models.Option.t_Option (t_Slice v_T)
        else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre
    =
    (fun (self_: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
        self_.Core_models.Ops.Range.f_start <=.
        (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) (out: t_Slice v_T) ->
        true);
    f_index
    =
    (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
        Rust_primitives.Slice.slice_slice #v_T
          slice
          self.Core_models.Ops.Range.f_start
          (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_get_unchecked_pre
    =
    (fun (self_: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
        self_.Core_models.Ops.Range.f_start <=.
        (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_get_unchecked_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) (out: t_Slice v_T) ->
        true);
    f_get_unchecked
    =
    fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
      Rust_primitives.Slice.slice_slice #v_T
        slice
        self.Core_models.Ops.Range.f_start
        (Rust_primitives.Slice.slice_length #v_T slice <: usize)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : t_SliceIndex (Core_models.Ops.Range.t_RangeTo usize) (t_Slice v_T) =
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
    (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) ->
        if
          self.Core_models.Ops.Range.f_end <=.
          (Rust_primitives.Slice.slice_length #v_T slice <: usize)
        then
          Core_models.Option.Option_Some
          (Rust_primitives.Slice.slice_slice #v_T
              slice
              (mk_usize 0)
              self.Core_models.Ops.Range.f_end)
          <:
          Core_models.Option.t_Option (t_Slice v_T)
        else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre
    =
    (fun (self_: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) ->
        self_.Core_models.Ops.Range.f_end <=.
        (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) (out: t_Slice v_T) ->
        true);
    f_index
    =
    (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) ->
        Rust_primitives.Slice.slice_slice #v_T slice (mk_usize 0) self.Core_models.Ops.Range.f_end);
    f_get_unchecked_pre
    =
    (fun (self_: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) ->
        self_.Core_models.Ops.Range.f_end <=.
        (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_get_unchecked_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) (out: t_Slice v_T) ->
        true);
    f_get_unchecked
    =
    fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) ->
      Rust_primitives.Slice.slice_slice #v_T slice (mk_usize 0) self.Core_models.Ops.Range.f_end
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : t_SliceIndex (Core_models.Ops.Range.t_Range usize) (t_Slice v_T) =
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
    (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) ->
        if
          self.Core_models.Ops.Range.f_start <=. self.Core_models.Ops.Range.f_end &&
          self.Core_models.Ops.Range.f_end <=.
          (Rust_primitives.Slice.slice_length #v_T slice <: usize)
        then
          Core_models.Option.Option_Some
          (Rust_primitives.Slice.slice_slice #v_T
              slice
              self.Core_models.Ops.Range.f_start
              self.Core_models.Ops.Range.f_end)
          <:
          Core_models.Option.t_Option (t_Slice v_T)
        else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre
    =
    (fun (self_: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) ->
        self_.Core_models.Ops.Range.f_start <=. self_.Core_models.Ops.Range.f_end &&
        self_.Core_models.Ops.Range.f_end <=.
        (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) (out: t_Slice v_T) -> true
    );
    f_index
    =
    (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) ->
        Rust_primitives.Slice.slice_slice #v_T
          slice
          self.Core_models.Ops.Range.f_start
          self.Core_models.Ops.Range.f_end);
    f_get_unchecked_pre
    =
    (fun (self_: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) ->
        self_.Core_models.Ops.Range.f_start <=. self_.Core_models.Ops.Range.f_end &&
        self_.Core_models.Ops.Range.f_end <=.
        (Rust_primitives.Slice.slice_length #v_T slice <: usize));
    f_get_unchecked_post
    =
    (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) (out: t_Slice v_T) -> true
    );
    f_get_unchecked
    =
    fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) ->
      Rust_primitives.Slice.slice_slice #v_T
        slice
        self.Core_models.Ops.Range.f_start
        self.Core_models.Ops.Range.f_end
  }

/// Generic `Index<I>` for `[T]`, matching std\'s
/// `impl<T, I: SliceIndex<[T]>> Index<I> for [T]`
/// in `core/src/slice/index.rs`. Body delegates to
/// `SliceIndex::get` (we removed the `index`/`index_mut` methods
/// from the trait to avoid modeling raw pointers; std would call
/// `index.index(self)` instead).
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_SliceIndex v_I (t_Slice v_T))
    : Core_models.Ops.Index.t_Index (t_Slice v_T) v_I =
  {
    f_Output = i0.f_Output;
    f_index_pre
    =
    (fun (self_: t_Slice v_T) (i: v_I) ->
        Core_models.Option.impl__is_some #i0.f_Output
          (f_get #v_I #(t_Slice v_T) #FStar.Tactics.Typeclasses.solve i self_
            <:
            Core_models.Option.t_Option i0.f_Output));
    f_index_post = (fun (self: t_Slice v_T) (i: v_I) (out: i0.f_Output) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (i: v_I) ->
      match
        f_get #v_I #(t_Slice v_T) #FStar.Tactics.Typeclasses.solve i self
        <:
        Core_models.Option.t_Option i0.f_Output
      with
      | Core_models.Option.Option_Some r -> r
      | Core_models.Option.Option_None  -> Core_models.Panicking.Internal.panic #i0.f_Output ()
  }
