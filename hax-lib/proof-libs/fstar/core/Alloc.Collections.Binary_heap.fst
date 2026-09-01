module Alloc.Collections.Binary_heap
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

open Rust_primitives.Notations

type t_BinaryHeap (v_T: Type0) (v_A: Type0) =
  | BinaryHeap : Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global -> Core_models.Marker.t_PhantomData v_A
    -> t_BinaryHeap v_T v_A

/// See [`std::collections::binary_heap::Iter`]
type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Iter v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Iter v_T) -> true);
    f_next_post
    =
    (fun (self: t_Iter v_T) (out1: (t_Iter v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Iter v_T) ->
      let (self: t_Iter v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Iter v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Iter v_T = { self with _0 = tmp0 } <: t_Iter v_T in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_Iter v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Iter v_T & Core_models.Option.t_Option v_T)
  }

/// See [`std::collections::BinaryHeap::new`]
let impl_9__new (#v_T: Type0) (_: Prims.unit) : t_BinaryHeap v_T Alloc.Alloc.t_Global =
  BinaryHeap
    (Alloc.Vec.from_seq #v_T
        #Alloc.Alloc.t_Global
        (Rust_primitives.Sequence.seq_empty #v_T () <: Rust_primitives.Sequence.t_Seq v_T))
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global)
  <:
  t_BinaryHeap v_T Alloc.Alloc.t_Global

/// See [`std::collections::BinaryHeap::with_capacity`]: capacity is
/// not modeled, so this is `new`.
let impl_9__with_capacity (#v_T: Type0) (e_capacity: usize) : t_BinaryHeap v_T Alloc.Alloc.t_Global =
  impl_9__new #v_T ()

/// See [`std::collections::BinaryHeap::new_in`]
let impl_10__new_in
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (e_alloc: v_A)
    : t_BinaryHeap v_T v_A =
  BinaryHeap
    (Alloc.Vec.from_seq #v_T
        #Alloc.Alloc.t_Global
        (Rust_primitives.Sequence.seq_empty #v_T () <: Rust_primitives.Sequence.t_Seq v_T))
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
  <:
  t_BinaryHeap v_T v_A

/// See [`std::collections::BinaryHeap::with_capacity_in`]
let impl_10__with_capacity_in
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (e_capacity: usize)
      (alloc: v_A)
    : t_BinaryHeap v_T v_A = impl_10__new_in #v_T #v_A alloc

/// See [`std::collections::BinaryHeap::retain`].
/// The loop walks from the back so a removal never shifts an
/// index still to be visited. `FnMut` is std\'s bound, and the body
/// is opaque for F* in exchange — see the note on
/// `VecDeque::retain`.
assume
val impl_10__retain':
    #v_T: Type0 ->
    #v_A: Type0 ->
    #v_F: Type0 ->
    {| i0: Alloc.Alloc.t_Allocator v_A |} ->
    {| i1: Core_models.Cmp.t_Ord v_T |} ->
    {| i2: Core_models.Ops.Function.t_FnMut v_F v_T |} ->
    self: t_BinaryHeap v_T v_A ->
    f: v_F
  -> t_BinaryHeap v_T v_A

unfold
let impl_10__retain
      (#v_T #v_A #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core_models.Ops.Function.t_FnMut v_F v_T)
     = impl_10__retain' #v_T #v_A #v_F #i0 #i1 #i2

/// See [`std::collections::BinaryHeap::into_sorted_vec`]: ascending.
/// Opaque: the Rust body below is the specification (repeatedly move
/// out the smallest remaining element), but proving the `Vec::push`
/// bound through the loop needs an invariant relating two locals,
/// which `hax_lib::loop_invariant!` cannot state here.
assume
val impl_10__into_sorted_vec':
    #v_T: Type0 ->
    #v_A: Type0 ->
    {| i0: Alloc.Alloc.t_Allocator v_A |} ->
    {| i1: Core_models.Cmp.t_Ord v_T |} ->
    self: t_BinaryHeap v_T v_A
  -> Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global

unfold
let impl_10__into_sorted_vec
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord v_T)
     = impl_10__into_sorted_vec' #v_T #v_A #i0 #i1

let impl_11__len
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : usize = Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global self._0

let impl_10__push
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord v_T)
      (self: t_BinaryHeap v_T v_A)
      (v: v_T)
    : Prims.Pure (t_BinaryHeap v_T v_A)
      (requires (impl_11__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_BinaryHeap v_T v_A =
    { self with _0 = Alloc.Vec.impl_1__push #v_T #Alloc.Alloc.t_Global self._0 v }
    <:
    t_BinaryHeap v_T v_A
  in
  self

let impl_10__pop
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord v_T)
      (self: t_BinaryHeap v_T v_A)
    : Prims.Pure (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let (self_e_future: t_BinaryHeap v_T v_A), (res: Core_models.Option.t_Option v_T) =
            temp_0_
          in
          ((impl_11__len #v_T #v_A self <: usize) >. mk_usize 0 <: bool) =.
          (Core_models.Option.impl__is_some #v_T res <: bool)) =
  let (max: Core_models.Option.t_Option v_T):Core_models.Option.t_Option v_T =
    Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  in
  let index:usize = mk_usize 0 in
  let (index: usize), (max: Core_models.Option.t_Option v_T) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (impl_11__len #v_T #v_A self <: usize)
      (fun temp_0_ i ->
          let (index: usize), (max: Core_models.Option.t_Option v_T) = temp_0_ in
          let i:usize = i in
          (i >. mk_usize 0 <: bool) =. (Core_models.Option.impl__is_some #v_T max <: bool) <: bool)
      (index, max <: (usize & Core_models.Option.t_Option v_T))
      (fun temp_0_ i ->
          let (index: usize), (max: Core_models.Option.t_Option v_T) = temp_0_ in
          let i:usize = i in
          if
            Core_models.Option.impl__is_none_or #v_T
              #(v_T -> bool)
              max
              (fun max ->
                  let max:v_T = max in
                  Core_models.Cmp.f_gt #v_T
                    #v_T
                    #FStar.Tactics.Typeclasses.solve
                    (self._0.[ i ] <: v_T)
                    max
                  <:
                  bool)
            <:
            bool
          then
            let max:Core_models.Option.t_Option v_T =
              Core_models.Option.Option_Some self._0.[ i ] <: Core_models.Option.t_Option v_T
            in
            let index:usize = i in
            index, max <: (usize & Core_models.Option.t_Option v_T)
          else index, max <: (usize & Core_models.Option.t_Option v_T))
  in
  let (self: t_BinaryHeap v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if Core_models.Option.impl__is_some #v_T max
    then
      let (tmp0: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global), (out: v_T) =
        Alloc.Vec.impl_1__remove #v_T #Alloc.Alloc.t_Global self._0 index
      in
      let self:t_BinaryHeap v_T v_A = { self with _0 = tmp0 } <: t_BinaryHeap v_T v_A in
      self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
      <:
      (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)
    else
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::BinaryHeap::append`]
let impl_10__append
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord v_T)
      (self other: t_BinaryHeap v_T v_A)
    : Prims.Pure (t_BinaryHeap v_T v_A & t_BinaryHeap v_T v_A)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (impl_11__len #v_T #v_A self <: usize)
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (impl_11__len #v_T #v_A other <: usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let
  (tmp0: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global), (tmp1: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global)
  =
    Alloc.Vec.impl_1__append #v_T #Alloc.Alloc.t_Global self._0 other._0
  in
  let self:t_BinaryHeap v_T v_A = { self with _0 = tmp0 } <: t_BinaryHeap v_T v_A in
  let other:t_BinaryHeap v_T v_A = { other with _0 = tmp1 } <: t_BinaryHeap v_T v_A in
  let _:Prims.unit = () in
  self, other <: (t_BinaryHeap v_T v_A & t_BinaryHeap v_T v_A)

/// See [`std::collections::BinaryHeap::is_empty`]
let impl_11__is_empty
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : bool = (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global self._0 <: usize) =. mk_usize 0

/// See [`std::collections::BinaryHeap::clear`]
let impl_11__clear
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : t_BinaryHeap v_T v_A =
  let self:t_BinaryHeap v_T v_A =
    {
      self with
      _0
      =
      Alloc.Vec.from_seq #v_T
        #Alloc.Alloc.t_Global
        (Rust_primitives.Sequence.seq_empty #v_T () <: Rust_primitives.Sequence.t_Seq v_T)
    }
    <:
    t_BinaryHeap v_T v_A
  in
  self

/// See [`std::collections::BinaryHeap::as_slice`]: arbitrary order,
/// which for this model is insertion order.
let impl_11__as_slice
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : t_Slice v_T = Alloc.Vec.impl_1__as_slice #v_T #Alloc.Alloc.t_Global self._0

/// See [`std::collections::BinaryHeap::into_vec`]: arbitrary order.
let impl_11__into_vec
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global = self._0

/// See [`std::collections::BinaryHeap::iter`]: arbitrary order.
let impl_11__iter
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : t_Iter v_T =
  Iter
  (Rust_primitives.Sequence.seq_from_slice #v_T
      (Alloc.Vec.impl_1__as_slice #v_T #Alloc.Alloc.t_Global self._0 <: t_Slice v_T))
  <:
  t_Iter v_T

/// See [`std::collections::BinaryHeap::reserve`]: capacity is not
/// modeled, so this leaves the contents untouched.
let impl_11__reserve
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
      (e_additional: usize)
    : t_BinaryHeap v_T v_A = self

/// See [`std::collections::BinaryHeap::reserve_exact`]
let impl_11__reserve_exact
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
      (e_additional: usize)
    : t_BinaryHeap v_T v_A = self

/// See [`std::collections::BinaryHeap::shrink_to_fit`]
let impl_11__shrink_to_fit
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : t_BinaryHeap v_T v_A = self

/// See [`std::collections::BinaryHeap::shrink_to`]
let impl_11__shrink_to
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
      (e_min_capacity: usize)
    : t_BinaryHeap v_T v_A = self

/// See [`std::collections::BinaryHeap::try_reserve`]: the model never
/// fails to allocate.
let impl_11__try_reserve
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
      (e_additional: usize)
    : (t_BinaryHeap v_T v_A &
      Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  in
  self, hax_temp_output
  <:
  (t_BinaryHeap v_T v_A & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  )

/// See [`std::collections::BinaryHeap::try_reserve_exact`]
let impl_11__try_reserve_exact
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
      (e_additional: usize)
    : (t_BinaryHeap v_T v_A &
      Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError) =
  let hax_temp_output:Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError =
    Core_models.Result.Result_Ok (() <: Prims.unit)
    <:
    Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  in
  self, hax_temp_output
  <:
  (t_BinaryHeap v_T v_A & Core_models.Result.t_Result Prims.unit Alloc.Collections.t_TryReserveError
  )

let impl_11__peek
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Alloc.Alloc.t_Allocator v_A)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core_models.Cmp.t_Ord v_T)
      (self: t_BinaryHeap v_T v_A)
    : Prims.Pure (Core_models.Option.t_Option v_T)
      Prims.l_True
      (ensures
        fun res ->
          let res:Core_models.Option.t_Option v_T = res in
          ((impl_11__len #v_T #v_A self <: usize) >. mk_usize 0 <: bool) =.
          (Core_models.Option.impl__is_some #v_T res <: bool)) =
  let (max: Core_models.Option.t_Option v_T):Core_models.Option.t_Option v_T =
    Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  in
  let max:Core_models.Option.t_Option v_T =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (impl_11__len #v_T #v_A self <: usize)
      (fun max i ->
          let max:Core_models.Option.t_Option v_T = max in
          let i:usize = i in
          (i >. mk_usize 0 <: bool) =. (Core_models.Option.impl__is_some #v_T max <: bool) <: bool)
      max
      (fun max i ->
          let max:Core_models.Option.t_Option v_T = max in
          let i:usize = i in
          if
            Core_models.Option.impl__is_none_or #v_T
              #(v_T -> bool)
              max
              (fun max ->
                  let max:v_T = max in
                  Core_models.Cmp.f_gt #v_T
                    #v_T
                    #FStar.Tactics.Typeclasses.solve
                    (self._0.[ i ] <: v_T)
                    max
                  <:
                  bool)
            <:
            bool
          then
            let max:Core_models.Option.t_Option v_T =
              Core_models.Option.Option_Some self._0.[ i ] <: Core_models.Option.t_Option v_T
            in
            max
          else max)
  in
  max

assume val lemma_peek_pop: #t:Type -> (#a: Type) -> (#i: Core_models.Cmp.t_Ord t) 
  -> (#i1: Alloc.Alloc.t_Allocator a) -> h: t_BinaryHeap t a
  -> Lemma (impl_11__peek h == snd (impl_10__pop h))
          [SMTPat (impl_11__peek #t #a h)]
