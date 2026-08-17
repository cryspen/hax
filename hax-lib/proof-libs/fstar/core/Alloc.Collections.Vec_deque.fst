module Alloc.Collections.Vec_deque
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_VecDeque (v_T: Type0) (v_A: Type0) =
  | VecDeque : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_VecDeque v_T v_A

/// Insert `value` at `index`, shifting the tail right. `Seq` has no
/// element-write primitive, so every positional update in this module
/// is spelled as this drain/push/concat surgery.
let seq_insert (#v_T: Type0) (s: Rust_primitives.Sequence.t_Seq v_T) (index: usize) (value: v_T)
    : Prims.Pure (Rust_primitives.Sequence.t_Seq v_T)
      (requires
        index <=. (Rust_primitives.Sequence.seq_len #v_T s <: usize) &&
        (Rust_primitives.Sequence.seq_len #v_T s <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let l:usize = Rust_primitives.Sequence.seq_len #v_T s in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_drain #v_T s index l
  in
  let s:Rust_primitives.Sequence.t_Seq v_T = tmp0 in
  let right:Rust_primitives.Sequence.t_Seq v_T = out in
  let s:Rust_primitives.Sequence.t_Seq v_T = Rust_primitives.Sequence.seq_push #v_T s value in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T s right
  in
  let s:Rust_primitives.Sequence.t_Seq v_T = tmp0 in
  let right:Rust_primitives.Sequence.t_Seq v_T = tmp1 in
  let _:Prims.unit = () in
  s

/// See [`std::collections::VecDeque::new`]
let impl_4__new (#v_T: Type0) (_: Prims.unit) : t_VecDeque v_T Alloc.Alloc.t_Global =
  VecDeque (Rust_primitives.Sequence.seq_empty #v_T ())
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global)
  <:
  t_VecDeque v_T Alloc.Alloc.t_Global

/// See [`std::collections::VecDeque::with_capacity`]
let impl_4__with_capacity (#v_T: Type0) (e_capacity: usize) : t_VecDeque v_T Alloc.Alloc.t_Global =
  impl_4__new #v_T ()

/// See [`std::collections::VecDeque::try_with_capacity`] (unstable
/// in std: `try_with_capacity`): the model never fails to
/// allocate, so this is always `Ok`.
let impl_4__try_with_capacity (#v_T: Type0) (e_capacity: usize)
    : Core_models.Result.t_Result (t_VecDeque v_T Alloc.Alloc.t_Global)
      Alloc.Collections.t_TryReserveError =
  Core_models.Result.Result_Ok (impl_4__new #v_T ())
  <:
  Core_models.Result.t_Result (t_VecDeque v_T Alloc.Alloc.t_Global)
    Alloc.Collections.t_TryReserveError

/// See [`std::collections::VecDeque::new_in`]
let impl_5__new_in (#v_T #v_A: Type0) (e_alloc: v_A) : t_VecDeque v_T v_A =
  VecDeque (Rust_primitives.Sequence.seq_empty #v_T ())
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
  <:
  t_VecDeque v_T v_A

/// See [`std::collections::VecDeque::with_capacity_in`]
let impl_5__with_capacity_in (#v_T #v_A: Type0) (e_capacity: usize) (alloc: v_A)
    : t_VecDeque v_T v_A = impl_5__new_in #v_T #v_A alloc

/// See [`std::collections::VecDeque::len`]
let impl_5__len (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : usize =
  Rust_primitives.Sequence.seq_len #v_T self._0

/// See [`std::collections::VecDeque::is_empty`]
let impl_5__is_empty (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : bool =
  (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0

/// See [`std::collections::VecDeque::get`]
let impl_5__get (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (index: usize)
    : Core_models.Option.t_Option v_T =
  if index <. (impl_5__len #v_T #v_A self <: usize)
  then
    Core_models.Option.Option_Some (Rust_primitives.Sequence.seq_index #v_T self._0 index)
    <:
    Core_models.Option.t_Option v_T
  else Core_models.Option.Option_None <: Core_models.Option.t_Option v_T

/// See [`std::collections::VecDeque::front`]
let impl_5__front (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : Core_models.Option.t_Option v_T =
  impl_5__get #v_T #v_A self (mk_usize 0)

/// See [`std::collections::VecDeque::back`]
let impl_5__back (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : Core_models.Option.t_Option v_T =
  if (impl_5__len #v_T #v_A self <: usize) =. mk_usize 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  else impl_5__get #v_T #v_A self ((impl_5__len #v_T #v_A self <: usize) -! mk_usize 1 <: usize)

/// See [`std::collections::VecDeque::pop_front`]
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

/// See [`std::collections::VecDeque::pop_back`]
let impl_5__pop_back (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A)
    : (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T) =
  let l:usize = impl_5__len #v_T #v_A self in
  let (self: t_VecDeque v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if l =. mk_usize 0
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
    else
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 (l -! mk_usize 1 <: usize)
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::VecDeque::remove`]
let impl_5__remove (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (index: usize)
    : (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T) =
  let (self: t_VecDeque v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if index <. (impl_5__len #v_T #v_A self <: usize)
    then
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 index
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::VecDeque::clear`]
let impl_5__clear (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : t_VecDeque v_T v_A =
  let self:t_VecDeque v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_empty #v_T () } <: t_VecDeque v_T v_A
  in
  self

/// See [`std::collections::VecDeque::truncate`]
let impl_5__truncate (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (len: usize) : t_VecDeque v_T v_A =
  let l:usize = impl_5__len #v_T #v_A self in
  let self:t_VecDeque v_T v_A =
    if len <. l
    then
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
        Rust_primitives.Sequence.seq_drain #v_T self._0 len l
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      let e_dropped:Rust_primitives.Sequence.t_Seq v_T = out in
      self
    else self
  in
  self

/// See [`std::collections::VecDeque::truncate_front`] (unstable in
/// std: `deque_truncate_front`): keeps the *last* `len` elements.
let impl_5__truncate_front (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (len: usize)
    : t_VecDeque v_T v_A =
  let l:usize = impl_5__len #v_T #v_A self in
  let self:t_VecDeque v_T v_A =
    if len <. l
    then
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
        Rust_primitives.Sequence.seq_drain #v_T self._0 (mk_usize 0) (l -! len <: usize)
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      let e_dropped:Rust_primitives.Sequence.t_Seq v_T = out in
      self
    else self
  in
  self

/// See [`std::collections::VecDeque::contains`].
/// Opaque for F* only: hax lowers a generic `PartialEq::eq` to F*\'s
/// primitive `=.`, which demands an `eqtype`, so the body does not
/// typecheck at an arbitrary `T` — the same reason
/// `core_models::slice::Slice::contains` is opaque.
assume
val impl_5__contains':
    #v_T: Type0 ->
    #v_A: Type0 ->
    {| i0: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    self: t_VecDeque v_T v_A ->
    x: v_T
  -> bool

unfold
let impl_5__contains
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_T)
     = impl_5__contains' #v_T #v_A #i0

/// See [`std::collections::VecDeque::as_slices`].
/// DEVIATION(std): the model\'s deque is always contiguous, so the
/// front slice is the whole deque and the back slice is always
/// empty. std only promises that the concatenation of the two is
/// the deque, which is what tests check.
let impl_5__as_slices (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : (t_Slice v_T & t_Slice v_T) =
  let s:t_Slice v_T = Rust_primitives.Sequence.seq_to_slice #v_T self._0 in
  s,
  Rust_primitives.Slice.slice_slice #v_T
    s
    (impl_5__len #v_T #v_A self <: usize)
    (impl_5__len #v_T #v_A self <: usize)
  <:
  (t_Slice v_T & t_Slice v_T)

/// See [`std::collections::VecDeque::iter`]
let impl_5__iter (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A)
    : Alloc.Collections.Vec_deque.Iter.t_Iter v_T =
  Alloc.Collections.Vec_deque.Iter.Iter
  (Rust_primitives.Sequence.seq_from_slice #v_T
      (Rust_primitives.Sequence.seq_to_slice #v_T self._0 <: t_Slice v_T))
  <:
  Alloc.Collections.Vec_deque.Iter.t_Iter v_T

/// See [`std::collections::VecDeque::reserve`]: capacity is not
/// modeled, so this leaves the contents untouched.
let impl_5__reserve (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (e_additional: usize)
    : t_VecDeque v_T v_A = self

/// See [`std::collections::VecDeque::reserve_exact`]
let impl_5__reserve_exact (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (e_additional: usize)
    : t_VecDeque v_T v_A = self

/// See [`std::collections::VecDeque::shrink_to_fit`]
let impl_5__shrink_to_fit (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) : t_VecDeque v_T v_A = self

/// See [`std::collections::VecDeque::shrink_to`]
let impl_5__shrink_to (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (e_min_capacity: usize)
    : t_VecDeque v_T v_A = self

/// See [`std::collections::VecDeque::try_reserve`]: the model never
/// fails to allocate.
let impl_5__try_reserve (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (e_additional: usize)
    : (t_VecDeque v_T v_A &
      Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  in
  self, hax_temp_output
  <:
  (t_VecDeque v_T v_A & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError)

/// See [`std::collections::VecDeque::try_reserve_exact`]
let impl_5__try_reserve_exact (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (e_additional: usize)
    : (t_VecDeque v_T v_A &
      Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  in
  self, hax_temp_output
  <:
  (t_VecDeque v_T v_A & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError)

/// See [`std::collections::VecDeque::retain`].
/// The loop walks indices from the back so that a removal never
/// shifts an index still to be visited; the invariant is what lets
/// the backend discharge `seq_remove`\'s bound.
assume
val impl_5__retain':
    #v_T: Type0 ->
    #v_A: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F v_T |} ->
    self: t_VecDeque v_T v_A ->
    f: v_F
  -> t_VecDeque v_T v_A

unfold
let impl_5__retain
      (#v_T #v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl_5__retain' #v_T #v_A #v_F #i0

/// See [`std::collections::VecDeque::resize_with`]
assume
val impl_5__resize_with':
    #v_T: Type0 ->
    #v_A: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F Prims.unit |} ->
    self: t_VecDeque v_T v_A ->
    new_len: usize ->
    generator: v_F
  -> t_VecDeque v_T v_A

unfold
let impl_5__resize_with
      (#v_T #v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F Prims.unit)
     = impl_5__resize_with' #v_T #v_A #v_F #i0

/// See [`std::collections::VecDeque::binary_search_by`]. Linear,
/// for the reason given on `binary_search`.
assume
val impl_5__binary_search_by':
    #v_T: Type0 ->
    #v_A: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_F v_T |} ->
    self: t_VecDeque v_T v_A ->
    f: v_F
  -> Core_models.Result.t_Result usize usize

unfold
let impl_5__binary_search_by
      (#v_T #v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl_5__binary_search_by' #v_T #v_A #v_F #i0

/// See [`std::collections::VecDeque::binary_search`].
/// DEVIATION(std): a linear scan for the first element that is not
/// `Less` than `x`, not a bisection. Like std the result is only
/// meaningful on a sorted deque; std explicitly leaves *which* of
/// several equal elements is returned unspecified, so returning the
/// first one is a legal implementation, and it is far easier to
/// reason about than a bisection.
let impl_5__binary_search
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (self: t_VecDeque v_T v_A)
      (x: v_T)
    : Core_models.Result.t_Result usize usize =
  impl_5__binary_search_by #v_T
    #v_A
    #(v_T -> Core_models.Cmp.t_Ordering)
    self
    (fun probe ->
        let probe:v_T = probe in
        Core_models.Cmp.f_cmp #v_T #FStar.Tactics.Typeclasses.solve probe x
        <:
        Core_models.Cmp.t_Ordering)

/// See [`std::collections::VecDeque::binary_search_by_key`].
/// The scan is spelled out rather than delegated to
/// `binary_search_by`: hax rejects a closure that calls a captured
/// `FnMut` (hax issue #1060).
assume
val impl_5__binary_search_by_key':
    #v_T: Type0 ->
    #v_A: Type0 ->
    #v_B: Type0 ->
    #v_F: Type0 ->
    {| i0: Core_models.Cmp.t_Ord v_B |} ->
    {| i1: Core_models.Ops.Function.t_Fn v_F v_T |} ->
    self: t_VecDeque v_T v_A ->
    b: v_B ->
    f: v_F
  -> Core_models.Result.t_Result usize usize

unfold
let impl_5__binary_search_by_key
      (#v_T #v_A #v_B #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Ops.Function.t_Fn v_F v_T)
     = impl_5__binary_search_by_key' #v_T #v_A #v_B #v_F #i0 #i1

/// See [`std::collections::VecDeque::partition_point`]
assume
val impl_5__partition_point':
    #v_T: Type0 ->
    #v_A: Type0 ->
    #v_P: Type0 ->
    {| i0: Core_models.Ops.Function.t_Fn v_P v_T |} ->
    self: t_VecDeque v_T v_A ->
    pred: v_P
  -> usize

unfold
let impl_5__partition_point
      (#v_T #v_A #v_P: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_Fn v_P v_T)
     = impl_5__partition_point' #v_T #v_A #v_P #i0

/// See [`std::collections::VecDeque::push_back`]
let impl_5__push_back (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (x: v_T)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires
        (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_VecDeque v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_push #v_T self._0 x } <: t_VecDeque v_T v_A
  in
  self

/// See [`std::collections::VecDeque::push_front`]
let impl_5__push_front (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (value: v_T)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires
        (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_VecDeque v_T v_A =
    { self with _0 = seq_insert #v_T self._0 (mk_usize 0) value } <: t_VecDeque v_T v_A
  in
  self

/// See [`std::collections::VecDeque::swap`]
let impl_5__swap (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (i j: usize)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires
        i <. (impl_5__len #v_T #v_A self <: usize) && j <. (impl_5__len #v_T #v_A self <: usize))
      (fun _ -> Prims.l_True) =
  let self:t_VecDeque v_T v_A =
    if i <>. j
    then
      let lo:usize = if i <. j then i else j in
      let hi:usize = if i <. j then j else i in
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 hi
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      let high:v_T = out in
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 lo
      in
      let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
      let low:v_T = out in
      let self:t_VecDeque v_T v_A =
        { self with _0 = seq_insert #v_T self._0 lo high } <: t_VecDeque v_T v_A
      in
      { self with _0 = seq_insert #v_T self._0 hi low } <: t_VecDeque v_T v_A
    else self
  in
  self

/// See [`std::collections::VecDeque::swap_remove_front`]
let impl_5__swap_remove_front (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (index: usize)
    : (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T) =
  let (self: t_VecDeque v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if index <. (impl_5__len #v_T #v_A self <: usize)
    then
      let self:t_VecDeque v_T v_A = impl_5__swap #v_T #v_A self index (mk_usize 0) in
      let (tmp0: t_VecDeque v_T v_A), (out: Core_models.Option.t_Option v_T) =
        impl_5__pop_front #v_T #v_A self
      in
      let self:t_VecDeque v_T v_A = tmp0 in
      self, out <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::VecDeque::swap_remove_back`]
let impl_5__swap_remove_back (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (index: usize)
    : (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T) =
  let l:usize = impl_5__len #v_T #v_A self in
  let (self: t_VecDeque v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if index <. l
    then
      let self:t_VecDeque v_T v_A = impl_5__swap #v_T #v_A self index (l -! mk_usize 1 <: usize) in
      let (tmp0: t_VecDeque v_T v_A), (out: Core_models.Option.t_Option v_T) =
        impl_5__pop_back #v_T #v_A self
      in
      let self:t_VecDeque v_T v_A = tmp0 in
      self, out <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_VecDeque v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::VecDeque::insert`]
let impl_5__insert (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (index: usize) (value: v_T)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires
        index <=. (impl_5__len #v_T #v_A self <: usize) &&
        (impl_5__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_VecDeque v_T v_A =
    { self with _0 = seq_insert #v_T self._0 index value } <: t_VecDeque v_T v_A
  in
  self

/// See [`std::collections::VecDeque::split_off`]
let impl_5__split_off (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (at: usize)
    : Prims.Pure (t_VecDeque v_T v_A & t_VecDeque v_T v_A)
      (requires at <=. (impl_5__len #v_T #v_A self <: usize))
      (fun _ -> Prims.l_True) =
  let l:usize = impl_5__len #v_T #v_A self in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_drain #v_T self._0 at l
  in
  let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
  let hax_temp_output:t_VecDeque v_T v_A =
    VecDeque out (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
    <:
    t_VecDeque v_T v_A
  in
  self, hax_temp_output <: (t_VecDeque v_T v_A & t_VecDeque v_T v_A)

/// See [`std::collections::VecDeque::append`]
let impl_5__append (#v_T #v_A: Type0) (self other: t_VecDeque v_T v_A)
    : Prims.Pure (t_VecDeque v_T v_A & t_VecDeque v_T v_A)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (impl_5__len #v_T #v_A self <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (impl_5__len #v_T #v_A other <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T self._0 other._0
  in
  let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
  let other:t_VecDeque v_T v_A = { other with _0 = tmp1 } <: t_VecDeque v_T v_A in
  let _:Prims.unit = () in
  let other:t_VecDeque v_T v_A =
    { other with _0 = Rust_primitives.Sequence.seq_empty #v_T () } <: t_VecDeque v_T v_A
  in
  self, other <: (t_VecDeque v_T v_A & t_VecDeque v_T v_A)

/// See [`std::collections::VecDeque::rotate_left`]
let impl_5__rotate_left (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (n: usize)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires n <=. (impl_5__len #v_T #v_A self <: usize))
      (fun _ -> Prims.l_True) =
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_drain #v_T self._0 (mk_usize 0) n
  in
  let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
  let head:Rust_primitives.Sequence.t_Seq v_T = out in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T self._0 head
  in
  let self:t_VecDeque v_T v_A = { self with _0 = tmp0 } <: t_VecDeque v_T v_A in
  let head:Rust_primitives.Sequence.t_Seq v_T = tmp1 in
  let _:Prims.unit = () in
  self

/// See [`std::collections::VecDeque::rotate_right`]
let impl_5__rotate_right (#v_T #v_A: Type0) (self: t_VecDeque v_T v_A) (n: usize)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires n <=. (impl_5__len #v_T #v_A self <: usize))
      (fun _ -> Prims.l_True) =
  let l:usize = impl_5__len #v_T #v_A self in
  let self:t_VecDeque v_T v_A = impl_5__rotate_left #v_T #v_A self (l -! n <: usize) in
  self

/// See [`std::collections::VecDeque::resize`]
let impl_6__resize
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_T)
      (self: t_VecDeque v_T v_A)
      (new_len: usize)
      (value: v_T)
    : Prims.Pure (t_VecDeque v_T v_A)
      (requires
        (Rust_primitives.Hax.Int.from_machine new_len <: Hax_lib.Int.t_Int) <
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let l:usize = impl_5__len #v_T #v_A self in
  let self:t_VecDeque v_T v_A =
    if new_len >. l
    then
      Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
        (new_len -! l <: usize)
        (fun self k ->
            let self:t_VecDeque v_T v_A = self in
            let k:usize = k in
            (Rust_primitives.Hax.Int.from_machine (Rust_primitives.Sequence.seq_len #v_T self._0
                  <:
                  usize)
              <:
              Hax_lib.Int.t_Int) =
            ((Rust_primitives.Hax.Int.from_machine l <: Hax_lib.Int.t_Int) +
              (Rust_primitives.Hax.Int.from_machine k <: Hax_lib.Int.t_Int)
              <:
              Hax_lib.Int.t_Int)
            <:
            bool)
        self
        (fun self k ->
            let self:t_VecDeque v_T v_A = self in
            let k:usize = k in
            {
              self with
              _0
              =
              Rust_primitives.Sequence.seq_push #v_T
                self._0
                (Core_models.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve value <: v_T)
              <:
              Rust_primitives.Sequence.t_Seq v_T
            }
            <:
            t_VecDeque v_T v_A)
    else impl_5__truncate #v_T #v_A self new_len
  in
  self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (#v_T #v_A: Type0) : Core_models.Ops.Index.t_Index (t_VecDeque v_T v_A) usize =
  {
    f_Output = v_T;
    f_index_pre
    =
    (fun (self_: t_VecDeque v_T v_A) (i: usize) -> i <. (impl_5__len #v_T #v_A self_ <: usize));
    f_index_post = (fun (self: t_VecDeque v_T v_A) (i: usize) (out: v_T) -> true);
    f_index
    =
    fun (self: t_VecDeque v_T v_A) (i: usize) -> Rust_primitives.Sequence.seq_index #v_T self._0 i
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_8': #v_T: Type0 -> #v_A: Type0
  -> Core_models.Iter.Traits.Collect.t_IntoIterator (t_VecDeque v_T v_A)

unfold
let impl_8 (#v_T #v_A: Type0) = impl_8' #v_T #v_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': #v_T: Type0
  -> Core_models.Iter.Traits.Collect.t_FromIterator (t_VecDeque v_T Alloc.Alloc.t_Global) v_T

unfold
let impl_9 (#v_T: Type0) = impl_9' #v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let update_at_usize (#v_T #v_A: Type0)
    : Rust_primitives.Hax.update_at_tc (t_VecDeque v_T v_A) usize =
  {
    super_index = impl_7 #v_T #v_A;
    // `i` is deliberately left unannotated: the class gives it the refinement
    // `f_index_pre self i` (here `i < len self`), and annotating it `usize`
    // would drop exactly the bound `Seq.upd` needs.
    update_at = (fun self i x -> VecDeque (FStar.Seq.upd self._0 (v i) x) self._1)
  }
