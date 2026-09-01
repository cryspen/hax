module Alloc.Collections.Btree.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_BTreeMap (v_K: Type0) (v_V: Type0) (v_A: Type0) =
  | BTreeMap : Rust_primitives.Sequence.t_Seq (v_K & v_V) -> Core_models.Marker.t_PhantomData v_A
    -> t_BTreeMap v_K v_V v_A

/// See [`std::collections::btree_map::UnorderedKeyError`]: the error
/// `CursorMut::insert_before`/`insert_after` return. The cursor API
/// itself is not modeled, so nothing here produces one.
type t_UnorderedKeyError = | UnorderedKeyError : t_UnorderedKeyError

/// See [`std::collections::btree_map::Iter`]
type t_Iter (v_K: Type0) (v_V: Type0) =
  | Iter : Rust_primitives.Sequence.t_Seq (v_K & v_V) -> t_Iter v_K v_V

/// See [`std::collections::btree_map::Keys`]
type t_Keys (v_K: Type0) (v_V: Type0) =
  | Keys : Rust_primitives.Sequence.t_Seq v_K -> Core_models.Marker.t_PhantomData v_V
    -> t_Keys v_K v_V

/// See [`std::collections::btree_map::Values`]
type t_Values (v_K: Type0) (v_V: Type0) =
  | Values : Rust_primitives.Sequence.t_Seq v_V -> Core_models.Marker.t_PhantomData v_K
    -> t_Values v_K v_V

/// See [`std::collections::btree_map::IntoKeys`]
type t_IntoKeys (v_K: Type0) (v_V: Type0) (v_A: Type0) =
  | IntoKeys : Rust_primitives.Sequence.t_Seq (v_K & v_V) -> Core_models.Marker.t_PhantomData v_A
    -> t_IntoKeys v_K v_V v_A

/// See [`std::collections::btree_map::IntoValues`]
type t_IntoValues (v_K: Type0) (v_V: Type0) (v_A: Type0) =
  | IntoValues : Rust_primitives.Sequence.t_Seq (v_K & v_V) -> Core_models.Marker.t_PhantomData v_A
    -> t_IntoValues v_K v_V v_A

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_K #v_V: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Iter v_K v_V) =
  {
    f_Item = (v_K & v_V);
    f_next_pre = (fun (self: t_Iter v_K v_V) -> true);
    f_next_post
    =
    (fun
        (self: t_Iter v_K v_V)
        (out1: (t_Iter v_K v_V & Core_models.Option.t_Option (v_K & v_V)))
        ->
        true);
    f_next
    =
    fun (self: t_Iter v_K v_V) ->
      let (self: t_Iter v_K v_V), (hax_temp_output: Core_models.Option.t_Option (v_K & v_V)) =
        if (Rust_primitives.Sequence.seq_len #(v_K & v_V) self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option (v_K & v_V))
          <:
          (t_Iter v_K v_V & Core_models.Option.t_Option (v_K & v_V))
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq (v_K & v_V)), (out: (v_K & v_V)) =
            Rust_primitives.Sequence.seq_remove #(v_K & v_V) self._0 (mk_usize 0)
          in
          let self:t_Iter v_K v_V = { self with _0 = tmp0 } <: t_Iter v_K v_V in
          let p:(v_K & v_V) = out in
          self,
          (Core_models.Option.Option_Some (p._1, p._2 <: (v_K & v_V))
            <:
            Core_models.Option.t_Option (v_K & v_V))
          <:
          (t_Iter v_K v_V & Core_models.Option.t_Option (v_K & v_V))
      in
      self, hax_temp_output <: (t_Iter v_K v_V & Core_models.Option.t_Option (v_K & v_V))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_K #v_V: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Keys v_K v_V) =
  {
    f_Item = v_K;
    f_next_pre = (fun (self: t_Keys v_K v_V) -> true);
    f_next_post
    =
    (fun (self: t_Keys v_K v_V) (out1: (t_Keys v_K v_V & Core_models.Option.t_Option v_K)) -> true);
    f_next
    =
    fun (self: t_Keys v_K v_V) ->
      let (self: t_Keys v_K v_V), (hax_temp_output: Core_models.Option.t_Option v_K) =
        if (Rust_primitives.Sequence.seq_len #v_K self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_K)
          <:
          (t_Keys v_K v_V & Core_models.Option.t_Option v_K)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_K), (out: v_K) =
            Rust_primitives.Sequence.seq_remove #v_K self._0 (mk_usize 0)
          in
          let self:t_Keys v_K v_V = { self with _0 = tmp0 } <: t_Keys v_K v_V in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_K)
          <:
          (t_Keys v_K v_V & Core_models.Option.t_Option v_K)
      in
      self, hax_temp_output <: (t_Keys v_K v_V & Core_models.Option.t_Option v_K)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_K #v_V: Type0) : Core_models.Iter.Traits.Iterator.t_Iterator (t_Values v_K v_V) =
  {
    f_Item = v_V;
    f_next_pre = (fun (self: t_Values v_K v_V) -> true);
    f_next_post
    =
    (fun (self: t_Values v_K v_V) (out1: (t_Values v_K v_V & Core_models.Option.t_Option v_V)) ->
        true);
    f_next
    =
    fun (self: t_Values v_K v_V) ->
      let (self: t_Values v_K v_V), (hax_temp_output: Core_models.Option.t_Option v_V) =
        if (Rust_primitives.Sequence.seq_len #v_V self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_V)
          <:
          (t_Values v_K v_V & Core_models.Option.t_Option v_V)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq v_V), (out: v_V) =
            Rust_primitives.Sequence.seq_remove #v_V self._0 (mk_usize 0)
          in
          let self:t_Values v_K v_V = { self with _0 = tmp0 } <: t_Values v_K v_V in
          self, (Core_models.Option.Option_Some out <: Core_models.Option.t_Option v_V)
          <:
          (t_Values v_K v_V & Core_models.Option.t_Option v_V)
      in
      self, hax_temp_output <: (t_Values v_K v_V & Core_models.Option.t_Option v_V)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3 (#v_K #v_V #v_A: Type0)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_IntoKeys v_K v_V v_A) =
  {
    f_Item = v_K;
    f_next_pre = (fun (self: t_IntoKeys v_K v_V v_A) -> true);
    f_next_post
    =
    (fun
        (self: t_IntoKeys v_K v_V v_A)
        (out1: (t_IntoKeys v_K v_V v_A & Core_models.Option.t_Option v_K))
        ->
        true);
    f_next
    =
    fun (self: t_IntoKeys v_K v_V v_A) ->
      let (self: t_IntoKeys v_K v_V v_A), (hax_temp_output: Core_models.Option.t_Option v_K) =
        if (Rust_primitives.Sequence.seq_len #(v_K & v_V) self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_K)
          <:
          (t_IntoKeys v_K v_V v_A & Core_models.Option.t_Option v_K)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq (v_K & v_V)), (out: (v_K & v_V)) =
            Rust_primitives.Sequence.seq_remove #(v_K & v_V) self._0 (mk_usize 0)
          in
          let self:t_IntoKeys v_K v_V v_A = { self with _0 = tmp0 } <: t_IntoKeys v_K v_V v_A in
          self, (Core_models.Option.Option_Some out._1 <: Core_models.Option.t_Option v_K)
          <:
          (t_IntoKeys v_K v_V v_A & Core_models.Option.t_Option v_K)
      in
      self, hax_temp_output <: (t_IntoKeys v_K v_V v_A & Core_models.Option.t_Option v_K)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4 (#v_K #v_V #v_A: Type0)
    : Core_models.Iter.Traits.Iterator.t_Iterator (t_IntoValues v_K v_V v_A) =
  {
    f_Item = v_V;
    f_next_pre = (fun (self: t_IntoValues v_K v_V v_A) -> true);
    f_next_post
    =
    (fun
        (self: t_IntoValues v_K v_V v_A)
        (out1: (t_IntoValues v_K v_V v_A & Core_models.Option.t_Option v_V))
        ->
        true);
    f_next
    =
    fun (self: t_IntoValues v_K v_V v_A) ->
      let (self: t_IntoValues v_K v_V v_A), (hax_temp_output: Core_models.Option.t_Option v_V) =
        if (Rust_primitives.Sequence.seq_len #(v_K & v_V) self._0 <: usize) =. mk_usize 0
        then
          self, (Core_models.Option.Option_None <: Core_models.Option.t_Option v_V)
          <:
          (t_IntoValues v_K v_V v_A & Core_models.Option.t_Option v_V)
        else
          let (tmp0: Rust_primitives.Sequence.t_Seq (v_K & v_V)), (out: (v_K & v_V)) =
            Rust_primitives.Sequence.seq_remove #(v_K & v_V) self._0 (mk_usize 0)
          in
          let self:t_IntoValues v_K v_V v_A = { self with _0 = tmp0 } <: t_IntoValues v_K v_V v_A in
          self, (Core_models.Option.Option_Some out._2 <: Core_models.Option.t_Option v_V)
          <:
          (t_IntoValues v_K v_V v_A & Core_models.Option.t_Option v_V)
      in
      self, hax_temp_output <: (t_IntoValues v_K v_V v_A & Core_models.Option.t_Option v_V)
  }

/// See [`std::collections::BTreeMap::new`]
val impl_18__new: #v_K: Type0 -> #v_V: Type0 -> Prims.unit
  -> Prims.Pure (t_BTreeMap v_K v_V Alloc.Alloc.t_Global) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::clear`]
val impl_19__clear
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_BTreeMap v_K v_V v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::new_in`]
val impl_19__new_in (#v_K #v_V #v_A: Type0) {| i0: Core_models.Clone.t_Clone v_A |} (e_alloc: v_A)
    : Prims.Pure (t_BTreeMap v_K v_V v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::get`]
val impl_20__get
      (#v_K #v_V #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_K v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_K |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeMap v_K v_V v_A)
      (key: v_Q)
    : Prims.Pure (Core_models.Option.t_Option v_V) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::get_key_value`]
val impl_20__get_key_value
      (#v_K #v_V #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_K v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_K |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeMap v_K v_V v_A)
      (k: v_Q)
    : Prims.Pure (Core_models.Option.t_Option (v_K & v_V)) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::contains_key`]
val impl_20__contains_key
      (#v_K #v_V #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_K v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_K |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeMap v_K v_V v_A)
      (key: v_Q)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::first_key_value`]
val impl_20__first_key_value
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_K |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (Core_models.Option.t_Option (v_K & v_V)) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::last_key_value`]
val impl_20__last_key_value
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_K |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (Core_models.Option.t_Option (v_K & v_V)) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::pop_first`]
val impl_20__pop_first
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_K |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & Core_models.Option.t_Option (v_K & v_V))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::pop_last`]
val impl_20__pop_last
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_K |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & Core_models.Option.t_Option (v_K & v_V))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::insert`]: on a key that is
/// already present the *value* is replaced and the old one
/// returned; the stored key is left alone, as in std.
/// No `#[hax_lib::requires]` on the length here: that would need
/// `#[hax_lib::attributes]` on the block, which moves it to the
/// end of hax's impl numbering and so off index 20. `seq_insert`
/// carries the bound instead.
val impl_20__insert
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_K |}
      (self: t_BTreeMap v_K v_V v_A)
      (key: v_K)
      (value: v_V)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & Core_models.Option.t_Option v_V)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::remove`]
val impl_20__remove
      (#v_K #v_V #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_K v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_K |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeMap v_K v_V v_A)
      (key: v_Q)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & Core_models.Option.t_Option v_V)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::remove_entry`]
val impl_20__remove_entry
      (#v_K #v_V #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Borrow.t_Borrow v_K v_Q |}
      {| i2: Core_models.Cmp.t_Ord v_K |}
      {| i3: Core_models.Cmp.t_Ord v_Q |}
      (self: t_BTreeMap v_K v_V v_A)
      (key: v_Q)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & Core_models.Option.t_Option (v_K & v_V))
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::append`]: on a shared key
/// the value from `other` wins.
val impl_20__append
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_K |}
      {| i2: Core_models.Clone.t_Clone v_A |}
      (self other: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & t_BTreeMap v_K v_V v_A)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::split_off`]: keeps the
/// entries with keys `< key`, returns those `>= key`.
val impl_20__split_off
      (#v_K #v_V #v_A #v_Q: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      {| i1: Core_models.Cmp.t_Ord v_Q |}
      {| i2: Core_models.Borrow.t_Borrow v_K v_Q |}
      {| i3: Core_models.Cmp.t_Ord v_K |}
      {| i4: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
      (key: v_Q)
    : Prims.Pure (t_BTreeMap v_K v_V v_A & t_BTreeMap v_K v_V v_A)
      Prims.l_True
      (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::into_keys`]
val impl_20__into_keys
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_IntoKeys v_K v_V v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::into_values`]
val impl_20__into_values
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_IntoValues v_K v_V v_A) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::len`]
val impl_92__len
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::is_empty`]
val impl_92__is_empty
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::iter`]
val impl_92__iter
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_Iter v_K v_V) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::keys`]
val impl_92__keys
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_Keys v_K v_V) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::collections::BTreeMap::values`]
val impl_92__values
      (#v_K #v_V #v_A: Type0)
      {| i0: Core_models.Clone.t_Clone v_A |}
      (self: t_BTreeMap v_K v_V v_A)
    : Prims.Pure (t_Values v_K v_V) Prims.l_True (fun _ -> Prims.l_True)
