module Alloc.Collections.Btree.Set
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_BTreeSet (v_T: Type0) (v_A: Type0) =
  | BTreeSet : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_BTreeSet v_T v_A

/// See [`std::collections::btree_set::Iter`]
type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

/// See [`std::collections::btree_set::Difference`]
type t_Difference (v_T: Type0) (v_A: Type0) =
  | Difference : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_Difference v_T v_A

/// See [`std::collections::btree_set::Intersection`]
type t_Intersection (v_T: Type0) (v_A: Type0) =
  | Intersection : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_Intersection v_T v_A

/// See [`std::collections::btree_set::Union`]
type t_Union (v_T: Type0) = | Union : Rust_primitives.Sequence.t_Seq v_T -> t_Union v_T

/// See [`std::collections::btree_set::SymmetricDifference`]
type t_SymmetricDifference (v_T: Type0) =
  | SymmetricDifference : Rust_primitives.Sequence.t_Seq v_T -> t_SymmetricDifference v_T

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

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T #v_A: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Difference v_T v_A) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Difference v_T v_A) -> true);
    f_next_post
    =
    (fun
        (self: t_Difference v_T v_A)
        (out1: (t_Difference v_T v_A & Core_models.Option.t_Option v_T))
        ->
        true);
    f_next
    =
    fun (self: t_Difference v_T v_A) ->
      let (self: t_Difference v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Difference v_T v_A & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Difference v_T v_A = { self with _0 = tmp0 } <: t_Difference v_T v_A in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_Difference v_T v_A & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Difference v_T v_A & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T #v_A: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Intersection v_T v_A) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Intersection v_T v_A) -> true);
    f_next_post
    =
    (fun
        (self: t_Intersection v_T v_A)
        (out1: (t_Intersection v_T v_A & Core_models.Option.t_Option v_T))
        ->
        true);
    f_next
    =
    fun (self: t_Intersection v_T v_A) ->
      let (self: t_Intersection v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Intersection v_T v_A & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Intersection v_T v_A = { self with _0 = tmp0 } <: t_Intersection v_T v_A in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_Intersection v_T v_A & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Intersection v_T v_A & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Union v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_Union v_T) -> true);
    f_next_post
    =
    (fun (self: t_Union v_T) (out1: (t_Union v_T & Core_models.Option.t_Option v_T)) -> true);
    f_next
    =
    fun (self: t_Union v_T) ->
      let (self: t_Union v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_Union v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_Union v_T = { self with _0 = tmp0 } <: t_Union v_T in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_Union v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_Union v_T & Core_models.Option.t_Option v_T)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_SymmetricDifference v_T) =
  {
    f_Item = v_T;
    f_next_pre = (fun (self: t_SymmetricDifference v_T) -> true);
    f_next_post
    =
    (fun
        (self: t_SymmetricDifference v_T)
        (out1: (t_SymmetricDifference v_T & Core_models.Option.t_Option v_T))
        ->
        true);
    f_next
    =
    fun (self: t_SymmetricDifference v_T) ->
      let (self: t_SymmetricDifference v_T), (hax_temp_output: Core_models.Option.t_Option v_T) =
        if (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
          <:
          (t_SymmetricDifference v_T & Core_models.Option.t_Option v_T)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
            Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
          in
          let self:t_SymmetricDifference v_T =
            { self with _0 = tmp0 } <: t_SymmetricDifference v_T
          in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
          <:
          (t_SymmetricDifference v_T & Core_models.Option.t_Option v_T)
      in
      self, hax_temp_output <: (t_SymmetricDifference v_T & Core_models.Option.t_Option v_T)
  }

/// See [`std::collections::BTreeSet::new`]
val impl_13__new: #v_T: Type0 -> Prims.unit
  -> Prims.Pure (t_BTreeSet v_T Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::new_in`]
val impl_14__new_in (#v_T #v_A: Type0) {| i0: Core_models.Clone.t_Clone v_A |} (e_alloc: v_A)
    : Prims.Pure (t_BTreeSet v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::len`]
val impl_14__len
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::is_empty`]
val impl_14__is_empty
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::clear`].
/// std repeats `A: Clone` here on top of the block\'s, and so
/// must we: the two bounds are two dictionary arguments.
val impl_14__clear
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure (t_BTreeSet v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::first`]
val impl_14__first
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure (Core_models.Option.t_Option v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::last`]
val impl_14__last
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure (Core_models.Option.t_Option v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::pop_first`]
val impl_14__pop_first
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure (t_BTreeSet v_T v_A & Core_models.Option.t_Option v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::pop_last`]
val impl_14__pop_last
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure (t_BTreeSet v_T v_A & Core_models.Option.t_Option v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::contains`]
val impl_14__contains
      (#v_T #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_T v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_T |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeSet v_T v_A)
      (value: v_Q)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::get`]
val impl_14__get
      (#v_T #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_T v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_T |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeSet v_T v_A)
      (value: v_Q)
    : Prims.Pure (Core_models.Option.t_Option v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::remove`]
val impl_14__remove
      (#v_T #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_T v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_T |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeSet v_T v_A)
      (value: v_Q)
    : Prims.Pure (t_BTreeSet v_T v_A & bool) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::take`]
val impl_14__take
      (#v_T #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_T v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_T |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeSet v_T v_A)
      (value: v_Q)
    : Prims.Pure (t_BTreeSet v_T v_A & Core_models.Option.t_Option v_T)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::split_off`]: keeps the
/// elements `< value`, returns those `>= value`.
val impl_14__split_off
      (#v_T #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_Q |}
      {| i2: Core_models.Borrow.t_Borrow v_T v_Q |}
      {| i3: Core_models.Cmp.t_Ord v_T |}
      {| i4: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeSet v_T v_A)
      (value: v_Q)
    : Prims.Pure (t_BTreeSet v_T v_A & t_BTreeSet v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::retain`]. `FnMut` is
/// std\'s bound and has to be matched — see the note on
/// `VecDeque::retain`.
val impl_14__retain
      (#v_T #v_A #v_F: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      {| i2: Core_models.Ops.Function.t_FnMut v_F v_T |}
      (self: t_BTreeSet v_T v_A)
      (f: v_F)
    : Prims.Pure (t_BTreeSet v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::iter`]
val impl_14__iter
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeSet v_T v_A)
    : Prims.Pure (t_Iter v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::is_subset`]
val impl_14__is_subset
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::is_superset`]
val impl_14__is_superset
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::is_disjoint`]
val impl_14__is_disjoint
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::difference`]
val impl_14__difference
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure (t_Difference v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::intersection`]
val impl_14__intersection
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure (t_Intersection v_T v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::union`]: ascending, each
/// element once, `self`\'s copy on a tie (as std does).
val impl_14__union
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure (t_Union v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::symmetric_difference`]
val impl_14__symmetric_difference
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure (t_SymmetricDifference v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::insert`]: `false` when an
/// equal element was already present, which is then kept.
val impl_14__insert
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self: t_BTreeSet v_T v_A)
      (value: v_T)
    : Prims.Pure (t_BTreeSet v_T v_A & bool)
      (requires (impl_14__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::replace`]: unlike `insert`,
/// the *new* element wins and the old one is returned.
val impl_14__replace
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      (self: t_BTreeSet v_T v_A)
      (value: v_T)
    : Prims.Pure (t_BTreeSet v_T v_A & Core_models.Option.t_Option v_T)
      (requires (impl_14__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeSet::append`]: elements from
/// `other` win over equal ones already in `self`.
val impl_14__append
      (#v_T #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      {| i2: Core_models.Clone.t_Clone v_A |}
      (self other: t_BTreeSet v_T v_A)
    : Prims.Pure (t_BTreeSet v_T v_A & t_BTreeSet v_T v_A) Prims.l_True (fun _ -> Prims.l_True)
