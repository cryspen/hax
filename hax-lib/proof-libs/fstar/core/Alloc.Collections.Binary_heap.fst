module Alloc.Collections.Binary_heap
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

open Rust_primitives.Notations

type t_BinaryHeap (v_T: Type0) (v_A: Type0) =
  | BinaryHeap : Alloc.Vec.t_Vec v_T v_A -> t_BinaryHeap v_T v_A

let impl_10__new
      (#v_T: Type0)
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (_: Prims.unit)
    : t_BinaryHeap v_T v_A =
  BinaryHeap
  (Alloc.Vec.Vec (Rust_primitives.Sequence.seq_empty #v_T ())
      (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
    <:
    Alloc.Vec.t_Vec v_T v_A)
  <:
  t_BinaryHeap v_T v_A

let impl_11__len
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (self: t_BinaryHeap v_T v_A)
    : usize = Alloc.Vec.impl_1__len #v_T #v_A self._0

let impl_10__push
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (self: t_BinaryHeap v_T v_A)
      (v: v_T)
    : Prims.Pure (t_BinaryHeap v_T v_A)
      (requires (impl_11__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_BinaryHeap v_T v_A =
    { self with _0 = Alloc.Vec.impl_1__push #v_T #v_A self._0 v } <: t_BinaryHeap v_T v_A
  in
  self

let impl_10__pop
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
      (self: t_BinaryHeap v_T v_A)
    : Prims.Pure (t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T)
      Prims.l_True
      (ensures
        fun temp_0_ ->
          let self_e_future, res:(t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T) =
            temp_0_
          in
          ((impl_11__len #v_T #v_A self <: usize) >. mk_usize 0 <: bool) =.
          (Core_models.Option.impl__is_some #v_T res <: bool)) =
  let (max: Core_models.Option.t_Option v_T):Core_models.Option.t_Option v_T =
    Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  in
  let index:usize = mk_usize 0 in
  let index, max:(usize & Core_models.Option.t_Option v_T) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (impl_11__len #v_T #v_A self <: usize)
      (fun temp_0_ i ->
          let index, max:(usize & Core_models.Option.t_Option v_T) = temp_0_ in
          let i:usize = i in
          (i >. mk_usize 0 <: bool) =. (Core_models.Option.impl__is_some #v_T max <: bool) <: bool)
      (index, max <: (usize & Core_models.Option.t_Option v_T))
      (fun temp_0_ i ->
          let index, max:(usize & Core_models.Option.t_Option v_T) = temp_0_ in
          let i:usize = i in
          if
            Core_models.Option.impl__is_none_or #v_T
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
  let self, hax_temp_output:(t_BinaryHeap v_T v_A & Core_models.Option.t_Option v_T) =
    if Core_models.Option.impl__is_some #v_T max
    then
      let tmp0, out:(Alloc.Vec.t_Vec v_T v_A & v_T) =
        Alloc.Vec.impl_1__remove #v_T #v_A self._0 index
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

let impl_11__peek
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_Ord v_T)
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

assume val lemma_peek_pop: #t:Type -> (#a: Type) -> (#i: Core_models.Cmp.t_Ord t) -> h: t_BinaryHeap t a
  -> Lemma (impl_11__peek h == snd (impl_10__pop h))
          [SMTPat (impl_11__peek #t #a h)]
