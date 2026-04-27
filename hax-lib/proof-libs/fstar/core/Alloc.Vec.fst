module Alloc.Vec
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Vec (v_T: Type0) (v_A: Type0) =
  | Vec : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_Vec v_T v_A

let from_elem
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (item: v_T)
      (len: usize)
    : t_Vec v_T Alloc.Alloc.t_Global =
  Vec (Rust_primitives.Sequence.seq_create #v_T item len)
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global)
  <:
  t_Vec v_T Alloc.Alloc.t_Global

let impl__new (#v_T: Type0) (_: Prims.unit) : t_Vec v_T Alloc.Alloc.t_Global =
  Vec (Rust_primitives.Sequence.seq_empty #v_T ())
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global)
  <:
  t_Vec v_T Alloc.Alloc.t_Global

let impl__with_capacity (#v_T: Type0) (e_c: usize) : t_Vec v_T Alloc.Alloc.t_Global =
  impl__new #v_T ()

let impl_1__len (#v_T #v_A: Type0) (self: t_Vec v_T v_A) : usize =
  Rust_primitives.Sequence.seq_len #v_T self._0

let impl_1__pop (#v_T #v_A: Type0) (self: t_Vec v_T v_A)
    : (t_Vec v_T v_A & Core_models.Option.t_Option v_T) =
  let l:usize = Rust_primitives.Sequence.seq_len #v_T self._0 in
  let (self: t_Vec v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if l >. mk_usize 0
    then
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 (l -! mk_usize 1 <: usize)
      in
      let self:t_Vec v_T v_A = { self with _0 = tmp0 } <: t_Vec v_T v_A in
      let last:v_T = out in
      self, (Core_models.Option.Option_Some last <: Core_models.Option.t_Option v_T)
      <:
      (t_Vec v_T v_A & Core_models.Option.t_Option v_T)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_Vec v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_Vec v_T v_A & Core_models.Option.t_Option v_T)

let impl_1__is_empty (#v_T #v_A: Type0) (self: t_Vec v_T v_A) : bool =
  (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0

let impl_1__as_slice (#v_T #v_A: Type0) (self: t_Vec v_T v_A) : t_Slice v_T =
  Rust_primitives.Sequence.seq_to_slice #v_T self._0

assume
val impl_1__truncate': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> n: usize
  -> t_Vec v_T v_A

unfold
let impl_1__truncate (#v_T #v_A: Type0) = impl_1__truncate' #v_T #v_A

assume
val impl_1__swap_remove': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> n: usize
  -> (t_Vec v_T v_A & v_T)

unfold
let impl_1__swap_remove (#v_T #v_A: Type0) = impl_1__swap_remove' #v_T #v_A

assume
val impl_1__remove': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> index: usize
  -> (t_Vec v_T v_A & v_T)

unfold
let impl_1__remove (#v_T #v_A: Type0) = impl_1__remove' #v_T #v_A

assume
val impl_1__clear': #v_T: Type0 -> #v_A: Type0 -> self: t_Vec v_T v_A -> t_Vec v_T v_A

unfold
let impl_1__clear (#v_T #v_A: Type0) = impl_1__clear' #v_T #v_A

assume
val impl_1__drain': #v_T: Type0 -> #v_A: Type0 -> #v_R: Type0 -> self: t_Vec v_T v_A -> e_range: v_R
  -> (t_Vec v_T v_A & Alloc.Vec.Drain.t_Drain v_T v_A)

unfold
let impl_1__drain (#v_T #v_A #v_R: Type0) = impl_1__drain' #v_T #v_A #v_R

let impl_1__push (#v_T #v_A: Type0) (self: t_Vec v_T v_A) (x: v_T)
    : Prims.Pure (t_Vec v_T v_A)
      (requires
        (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_Vec v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_push #v_T self._0 x } <: t_Vec v_T v_A
  in
  self

let impl_1__insert (#v_T #v_A: Type0) (self: t_Vec v_T v_A) (index: usize) (element: v_T)
    : Prims.Pure (t_Vec v_T v_A)
      (requires
        index <=. (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) &&
        (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let l:usize = Rust_primitives.Sequence.seq_len #v_T self._0 in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_drain #v_T self._0 index l
  in
  let self:t_Vec v_T v_A = { self with _0 = tmp0 } <: t_Vec v_T v_A in
  let right:Rust_primitives.Sequence.t_Seq v_T = out in
  let self:t_Vec v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_push #v_T self._0 element } <: t_Vec v_T v_A
  in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T self._0 right
  in
  let self:t_Vec v_T v_A = { self with _0 = tmp0 } <: t_Vec v_T v_A in
  let right:Rust_primitives.Sequence.t_Seq v_T = tmp1 in
  let _:Prims.unit = () in
  self

assume
val impl_1__resize':
    #v_T: Type0 ->
    #v_A: Type0 ->
    self: t_Vec v_T v_A ->
    new_size: usize ->
    value: v_T
  -> Prims.Pure (t_Vec v_T v_A)
      Prims.l_True
      (ensures
        fun self_e_future ->
          let self_e_future:t_Vec v_T v_A = self_e_future in
          (impl_1__len #v_T #v_A self_e_future <: usize) =. new_size)

unfold
let impl_1__resize (#v_T #v_A: Type0) = impl_1__resize' #v_T #v_A

let impl_1__append (#v_T #v_A: Type0) (self other: t_Vec v_T v_A)
    : Prims.Pure (t_Vec v_T v_A & t_Vec v_T v_A)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (impl_1__len #v_T #v_A self <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (impl_1__len #v_T #v_A other <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T self._0 other._0
  in
  let self:t_Vec v_T v_A = { self with _0 = tmp0 } <: t_Vec v_T v_A in
  let other:t_Vec v_T v_A = { other with _0 = tmp1 } <: t_Vec v_T v_A in
  let _:Prims.unit = () in
  let other:t_Vec v_T v_A =
    { other with _0 = Rust_primitives.Sequence.seq_empty #v_T () } <: t_Vec v_T v_A
  in
  self, other <: (t_Vec v_T v_A & t_Vec v_T v_A)

let impl_2__extend_from_slice
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (self: t_Vec v_T v_A)
      (other: t_Slice v_T)
    : Prims.Pure (t_Vec v_T v_A)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (Rust_primitives.Sequence.seq_len #v_T self._0
                <:
                usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #v_T other <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let self:t_Vec v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_extend #v_T self._0 other } <: t_Vec v_T v_A
  in
  self

/// Generic `Index<I>` impl for `Vec`, matching std\'s
/// `impl<T, I: SliceIndex<[T]>, A: Allocator> Index<I> for Vec<T, A>`
/// (in `alloc/src/vec/mod.rs`). Delegates through `Deref` to the
/// `<[T]>::index` impl, the same body std uses. We omit the
/// `A: Allocator` bound because we do not model `Allocator` as a
/// trait — functionally identical for our purposes. The trait bound
/// references `std::slice::SliceIndex` (the real one) rather than
/// `core_models::slice::index::SliceIndex` because this crate is
/// standalone and does not depend on `core_models`; Aeneas\'s name
/// map for `std::slice::SliceIndex` aligns the extracted Lean path
/// with `core_models`\'s SliceIndex extraction (both extract under
/// `core.slice.index.SliceIndex`).
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (#v_T #v_I #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i0:
          Core_models.Slice.Index.t_SliceIndex v_I (t_Slice v_T))
    : Core_models.Ops.Index.t_Index (t_Vec v_T v_A) v_I =
  {
    f_Output = i0.f_Output;
    f_index_pre = (fun (self: t_Vec v_T v_A) (i: v_I) -> true);
    f_index_post = (fun (self: t_Vec v_T v_A) (i: v_I) (out: i0.f_Output) -> true);
    f_index = fun (self: t_Vec v_T v_A) (i: v_I) -> (impl_1__as_slice self <: t_Slice v_T).[ i ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T #v_A: Type0) : Core_models.Ops.Deref.t_Deref (t_Vec v_T v_A) =
  {
    f_Target = t_Slice v_T;
    f_deref_pre = (fun (self: t_Vec v_T v_A) -> true);
    f_deref_post = (fun (self: t_Vec v_T v_A) (out: t_Slice v_T) -> true);
    f_deref = fun (self: t_Vec v_T v_A) -> impl_1__as_slice #v_T #v_A self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': #v_T: Type0
  -> Core_models.Iter.Traits.Collect.t_FromIterator (t_Vec v_T Alloc.Alloc.t_Global) v_T

unfold
let impl_5 (#v_T: Type0) = impl_5' #v_T
