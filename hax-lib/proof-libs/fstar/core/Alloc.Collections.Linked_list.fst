module Alloc.Collections.Linked_list
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_LinkedList (v_T: Type0) (v_A: Type0) =
  | LinkedList : Rust_primitives.Sequence.t_Seq v_T -> Core_models.Marker.t_PhantomData v_A
    -> t_LinkedList v_T v_A

/// The shared-borrow iterator returned by
/// [`std::collections::LinkedList::iter`].
type t_Iter (v_T: Type0) = | Iter : Rust_primitives.Sequence.t_Seq v_T -> t_Iter v_T

/// See [`std::collections::LinkedList::new`]
let impl_7__new (#v_T: Type0) (_: Prims.unit) : t_LinkedList v_T Alloc.Alloc.t_Global =
  LinkedList (Rust_primitives.Sequence.seq_empty #v_T ())
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData Alloc.Alloc.t_Global)
  <:
  t_LinkedList v_T Alloc.Alloc.t_Global

/// See [`std::collections::LinkedList::new_in`]
let impl_8__new_in (#v_T #v_A: Type0) (e_alloc: v_A) : t_LinkedList v_T v_A =
  LinkedList (Rust_primitives.Sequence.seq_empty #v_T ())
    (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
  <:
  t_LinkedList v_T v_A

/// See [`std::collections::LinkedList::len`]
let impl_8__len (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) : usize =
  Rust_primitives.Sequence.seq_len #v_T self._0

/// See [`std::collections::LinkedList::append`]
let impl_7__append (#v_T: Type0) (self other: t_LinkedList v_T Alloc.Alloc.t_Global)
    : Prims.Pure (t_LinkedList v_T Alloc.Alloc.t_Global & t_LinkedList v_T Alloc.Alloc.t_Global)
      (requires
        ((Rust_primitives.Hax.Int.from_machine (impl_8__len #v_T #Alloc.Alloc.t_Global self <: usize
              )
            <:
            Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine (impl_8__len #v_T #Alloc.Alloc.t_Global other
                <:
                usize)
            <:
            Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine Core_models.Num.impl_usize__MAX <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T self._0 other._0
  in
  let self:t_LinkedList v_T Alloc.Alloc.t_Global =
    { self with _0 = tmp0 } <: t_LinkedList v_T Alloc.Alloc.t_Global
  in
  let other:t_LinkedList v_T Alloc.Alloc.t_Global =
    { other with _0 = tmp1 } <: t_LinkedList v_T Alloc.Alloc.t_Global
  in
  let _:Prims.unit = () in
  let other:t_LinkedList v_T Alloc.Alloc.t_Global =
    { other with _0 = Rust_primitives.Sequence.seq_empty #v_T () }
    <:
    t_LinkedList v_T Alloc.Alloc.t_Global
  in
  self, other <: (t_LinkedList v_T Alloc.Alloc.t_Global & t_LinkedList v_T Alloc.Alloc.t_Global)

/// See [`std::collections::LinkedList::is_empty`]
let impl_8__is_empty (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) : bool =
  (Rust_primitives.Sequence.seq_len #v_T self._0 <: usize) =. mk_usize 0

/// See [`std::collections::LinkedList::clear`]
let impl_8__clear (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) : t_LinkedList v_T v_A =
  let self:t_LinkedList v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_empty #v_T () } <: t_LinkedList v_T v_A
  in
  self

/// See [`std::collections::LinkedList::front`]
let impl_8__front (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) : Core_models.Option.t_Option v_T =
  if (impl_8__len #v_T #v_A self <: usize) =. mk_usize 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  else
    Core_models.Option.Option_Some (Rust_primitives.Sequence.seq_index #v_T self._0 (mk_usize 0))
    <:
    Core_models.Option.t_Option v_T

/// See [`std::collections::LinkedList::back`]
let impl_8__back (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) : Core_models.Option.t_Option v_T =
  let l:usize = impl_8__len #v_T #v_A self in
  if l =. mk_usize 0
  then Core_models.Option.Option_None <: Core_models.Option.t_Option v_T
  else
    Core_models.Option.Option_Some
    (Rust_primitives.Sequence.seq_index #v_T self._0 (l -! mk_usize 1 <: usize))
    <:
    Core_models.Option.t_Option v_T

/// See [`std::collections::LinkedList::pop_front`]
let impl_8__pop_front (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A)
    : (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T) =
  let (self: t_LinkedList v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if (impl_8__len #v_T #v_A self <: usize) =. mk_usize 0
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T)
    else
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 (mk_usize 0)
      in
      let self:t_LinkedList v_T v_A = { self with _0 = tmp0 } <: t_LinkedList v_T v_A in
      self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
      <:
      (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::LinkedList::pop_back`]
let impl_8__pop_back (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A)
    : (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T) =
  let l:usize = impl_8__len #v_T #v_A self in
  let (self: t_LinkedList v_T v_A), (hax_temp_output: Core_models.Option.t_Option v_T) =
    if l =. mk_usize 0
    then
      self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_T)
      <:
      (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T)
    else
      let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
        Rust_primitives.Sequence.seq_remove #v_T self._0 (l -! mk_usize 1 <: usize)
      in
      let self:t_LinkedList v_T v_A = { self with _0 = tmp0 } <: t_LinkedList v_T v_A in
      self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_T)
      <:
      (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T)
  in
  self, hax_temp_output <: (t_LinkedList v_T v_A & Core_models.Option.t_Option v_T)

/// See [`std::collections::LinkedList::contains`].
/// Opaque for F* only, for the same reason as
/// `VecDeque::contains`: hax lowers a generic `PartialEq::eq` to
/// F*\'s primitive `=.`, which demands an `eqtype`.
assume
val impl_8__contains':
    #v_T: Type0 ->
    #v_A: Type0 ->
    {| i0: Core_models.Cmp.t_PartialEq v_T v_T |} ->
    self: t_LinkedList v_T v_A ->
    x: v_T
  -> bool

unfold
let impl_8__contains
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Cmp.t_PartialEq v_T v_T)
     = impl_8__contains' #v_T #v_A #i0

/// See [`std::collections::LinkedList::iter`]
let impl_8__iter (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) : t_Iter v_T =
  Iter
  (Rust_primitives.Sequence.seq_from_slice #v_T
      (Rust_primitives.Sequence.seq_to_slice #v_T self._0 <: t_Slice v_T))
  <:
  t_Iter v_T

/// See [`std::collections::LinkedList::push_front`]
let impl_8__push_front (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) (elt: v_T)
    : Prims.Pure (t_LinkedList v_T v_A)
      (requires (impl_8__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let l:usize = Rust_primitives.Sequence.seq_len #v_T self._0 in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_drain #v_T self._0 (mk_usize 0) l
  in
  let self:t_LinkedList v_T v_A = { self with _0 = tmp0 } <: t_LinkedList v_T v_A in
  let right:Rust_primitives.Sequence.t_Seq v_T = out in
  let self:t_LinkedList v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_push #v_T self._0 elt } <: t_LinkedList v_T v_A
  in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (tmp1: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_concat #v_T self._0 right
  in
  let self:t_LinkedList v_T v_A = { self with _0 = tmp0 } <: t_LinkedList v_T v_A in
  let right:Rust_primitives.Sequence.t_Seq v_T = tmp1 in
  let _:Prims.unit = () in
  self

/// See [`std::collections::LinkedList::push_back`]
let impl_8__push_back (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) (elt: v_T)
    : Prims.Pure (t_LinkedList v_T v_A)
      (requires (impl_8__len #v_T #v_A self <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True) =
  let self:t_LinkedList v_T v_A =
    { self with _0 = Rust_primitives.Sequence.seq_push #v_T self._0 elt } <: t_LinkedList v_T v_A
  in
  self

/// See [`std::collections::LinkedList::split_off`]
let impl_8__split_off
      (#v_T #v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Clone.t_Clone v_A)
      (self: t_LinkedList v_T v_A)
      (at: usize)
    : Prims.Pure (t_LinkedList v_T v_A & t_LinkedList v_T v_A)
      (requires at <=. (impl_8__len #v_T #v_A self <: usize))
      (fun _ -> Prims.l_True) =
  let l:usize = impl_8__len #v_T #v_A self in
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: Rust_primitives.Sequence.t_Seq v_T) =
    Rust_primitives.Sequence.seq_drain #v_T self._0 at l
  in
  let self:t_LinkedList v_T v_A = { self with _0 = tmp0 } <: t_LinkedList v_T v_A in
  let hax_temp_output:t_LinkedList v_T v_A =
    LinkedList out (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_A)
    <:
    t_LinkedList v_T v_A
  in
  self, hax_temp_output <: (t_LinkedList v_T v_A & t_LinkedList v_T v_A)

/// See [`std::collections::LinkedList::remove`] (unstable in std:
/// `linked_list_remove`): removes and returns the element at `at`,
/// panicking when `at` is out of bounds.
let impl_8__remove (#v_T #v_A: Type0) (self: t_LinkedList v_T v_A) (at: usize)
    : Prims.Pure (t_LinkedList v_T v_A & v_T)
      (requires at <. (impl_8__len #v_T #v_A self <: usize))
      (fun _ -> Prims.l_True) =
  let (tmp0: Rust_primitives.Sequence.t_Seq v_T), (out: v_T) =
    Rust_primitives.Sequence.seq_remove #v_T self._0 at
  in
  let self:t_LinkedList v_T v_A = { self with _0 = tmp0 } <: t_LinkedList v_T v_A in
  let hax_temp_output:v_T = out in
  self, hax_temp_output <: (t_LinkedList v_T v_A & v_T)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_T: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Iter v_T) =
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
