module Alloc.Collections.Binary_heap
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

open Rust_primitives.Notations

type t_BinaryHeap (v_T: Type0) (v_A: Type0) =
  | BinaryHeap : Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global -> Core_models.Marker.t_PhantomData v_A
    -> t_BinaryHeap v_T v_A

let impl_10__new
      (#v_T: Type0)
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
      (_: Prims.unit)
    : t_BinaryHeap v_T v_A =
  BinaryHeap
    (Alloc.Vec.from_seq #v_T
        #Alloc.Alloc.t_Global
        (Rust_primitives.Sequence.seq_empty #v_T () <: Rust_primitives.Sequence.t_Seq v_T))
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
  <:
  t_BinaryHeap v_T v_A

assume
val impl_10__sift_up':
    #v_T: Type0 ->
    #v_A: Type0 ->
    {| i0: Core_models.Cmp.t_Ord v_T |} ->
    {| i1: Alloc.Alloc.t_Allocator v_A |} ->
    self: t_BinaryHeap v_T v_A ->
    start: usize ->
    pos: usize
  -> t_BinaryHeap v_T v_A

unfold
let impl_10__sift_up
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
     = impl_10__sift_up' #v_T #v_A #i0 #i1

/// Descends to a leaf and climbs back, unlike the textbook
/// `sift_down`, which leaves a different array on equal elements.
assume
val impl_10__sift_down_to_bottom':
    #v_T: Type0 ->
    #v_A: Type0 ->
    {| i0: Core_models.Cmp.t_Ord v_T |} ->
    {| i1: Alloc.Alloc.t_Allocator v_A |} ->
    self: t_BinaryHeap v_T v_A ->
    pos: usize
  -> t_BinaryHeap v_T v_A

unfold
let impl_10__sift_down_to_bottom
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
     = impl_10__sift_down_to_bottom' #v_T #v_A #i0 #i1

let impl_11__len
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : usize = Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global self._0

let impl_10__push
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
      (v: v_T)
    : Prims.Pure (t_BinaryHeap v_T v_A)
      (requires (impl_11__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let old_len:usize = impl_11__len #v_T #v_A self in
  let self:t_BinaryHeap v_T v_A =
    { self with _0 = Alloc.Vec.impl_1__push #v_T #Alloc.Alloc.t_Global self._0 v }
    <:
    t_BinaryHeap v_T v_A
  in
  let self:t_BinaryHeap v_T v_A = impl_10__sift_up #v_T #v_A self (mk_usize 0) old_len in
  self

let impl_10__pop
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
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
  let (self: t_BinaryHeap v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if (impl_11__len #v_T #v_A self <: usize) =. mk_usize 0
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)
    else
      let (tmp0: Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global), (out: v_T) =
        Alloc.Vec.impl_1__swap_remove #v_T #Alloc.Alloc.t_Global self._0 (mk_usize 0)
      in
      let self:t_BinaryHeap v_T v_A = { self with _0 = tmp0 } <: t_BinaryHeap v_T v_A in
      let root:v_T = out in
      let self:t_BinaryHeap v_T v_A =
        if ~.(Alloc.Vec.impl_1__is_empty #v_T #Alloc.Alloc.t_Global self._0 <: bool)
        then
          let self:t_BinaryHeap v_T v_A =
            impl_10__sift_down_to_bottom #v_T #v_A self (mk_usize 0)
          in
          self
        else self
      in
      self, (Core_models.Option.Option_Some root <: Core_models.Option.t_Option v_T)
      <:
      (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)

let impl_11__peek
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Alloc.Alloc.t_Allocator v_A)
      (self: t_BinaryHeap v_T v_A)
    : Prims.Pure (Core_models.Option.t_Option v_T)
      Prims.l_True
      (ensures
        fun res ->
          let res:Core_models.Option.t_Option v_T = res in
          ((impl_11__len #v_T #v_A self <: usize) >. mk_usize 0 <: bool) =.
          (Core_models.Option.impl__is_some #v_T res <: bool)) =
  if (impl_11__len #v_T #v_A self <: usize) =. mk_usize 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  else Core_models.Option.Option_Some self._0.[ mk_usize 0 ] <: Core_models.Option.t_Option v_T

assume val lemma_peek_pop: #t:Type -> (#a: Type) -> (#i: Core_models.Cmp.t_Ord t) 
  -> (#i1: Alloc.Alloc.t_Allocator a) -> h: t_BinaryHeap t a
  -> Lemma (impl_11__peek h == snd (impl_10__pop h))
          [SMTPat (impl_11__peek #t #a h)]
