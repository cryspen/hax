module Core_models.Slice.Index
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::slice::SliceIndex`]. We model the safe methods only;
/// `get_unchecked`/`get_unchecked_mut` would require raw-pointer
/// machinery and `*const`/`*mut` semantics we don\'t have. The
/// `&mut`-flavored `get_mut`/`index_mut` are also omitted — they
/// need a back-edge tuple shape and aren\'t required by anything
/// downstream Aeneas extraction emits in our test crate yet.
class t_SliceIndex (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Output:Type0;
  f_get_pre:self_: v_Self -> slice: v_T -> pred: Type0{true ==> pred};
  f_get_post:v_Self -> v_T -> Core_models.Option.t_Option f_Output -> Type0;
  f_get:x0: v_Self -> x1: v_T
    -> Prims.Pure (Core_models.Option.t_Option f_Output)
        (f_get_pre x0 x1)
        (fun result -> f_get_post x0 x1 result);
  f_index_pre:self_: v_Self -> slice: v_T -> pred: Type0{true ==> pred};
  f_index_post:v_Self -> v_T -> f_Output -> Type0;
  f_index:x0: v_Self -> x1: v_T
    -> Prims.Pure f_Output (f_index_pre x0 x1) (fun result -> f_index_post x0 x1 result)
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
        if self <. (Core_models.Slice.impl__len #v_T slice <: usize)
        then
          Core_models.Option.Option_Some (Rust_primitives.Slice.slice_index #v_T slice self)
          <:
          Core_models.Option.t_Option v_T
        else Core_models.Option.Option_None <: Core_models.Option.t_Option v_T);
    f_index_pre = (fun (self: usize) (slice: t_Slice v_T) -> true);
    f_index_post = (fun (self: usize) (slice: t_Slice v_T) (out: v_T) -> true);
    f_index
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
    f_index = fun (self: Core_models.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> slice
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
        if self.Core_models.Ops.Range.f_start <=. (Core_models.Slice.impl__len #v_T slice <: usize)
        then
          Core_models.Option.Option_Some
          (Rust_primitives.Slice.slice_slice #v_T
              slice
              self.Core_models.Ops.Range.f_start
              (Core_models.Slice.impl__len #v_T slice <: usize))
          <:
          Core_models.Option.t_Option (t_Slice v_T)
        else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre = (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) -> true);
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) (out: t_Slice v_T) ->
        true);
    f_index
    =
    fun (self: Core_models.Ops.Range.t_RangeFrom usize) (slice: t_Slice v_T) ->
      Rust_primitives.Slice.slice_slice #v_T
        slice
        self.Core_models.Ops.Range.f_start
        (Core_models.Slice.impl__len #v_T slice <: usize)
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
        if self.Core_models.Ops.Range.f_end <=. (Core_models.Slice.impl__len #v_T slice <: usize)
        then
          Core_models.Option.Option_Some
          (Rust_primitives.Slice.slice_slice #v_T
              slice
              (mk_usize 0)
              self.Core_models.Ops.Range.f_end)
          <:
          Core_models.Option.t_Option (t_Slice v_T)
        else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre = (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) -> true);
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_RangeTo usize) (slice: t_Slice v_T) (out: t_Slice v_T) ->
        true);
    f_index
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
          self.Core_models.Ops.Range.f_end <=. (Core_models.Slice.impl__len #v_T slice <: usize)
        then
          Core_models.Option.Option_Some
          (Rust_primitives.Slice.slice_slice #v_T
              slice
              self.Core_models.Ops.Range.f_start
              self.Core_models.Ops.Range.f_end)
          <:
          Core_models.Option.t_Option (t_Slice v_T)
        else Core_models.Option.Option_None <: Core_models.Option.t_Option (t_Slice v_T));
    f_index_pre = (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) -> true);
    f_index_post
    =
    (fun (self: Core_models.Ops.Range.t_Range usize) (slice: t_Slice v_T) (out: t_Slice v_T) -> true
    );
    f_index
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
    f_index_pre = (fun (self: t_Slice v_T) (i: v_I) -> true);
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
      | Core_models.Option.Option_None  ->
        Rust_primitives.Hax.never_to_any (Core_models.Panicking.panic_fmt (Core_models.Fmt.Rt.impl_1__new_const
                  (mk_usize 1)
                  (let list = ["slice index out of bounds"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core_models.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
  }
