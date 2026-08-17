module Alloc.Collections.Btree
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// Index of the first element of the *sorted* `s` that is not `Less`
/// than `key`, plus whether that element compares `Equal`. Every lookup
/// in the sorted-`Seq` model of `BTreeSet`/`BTreeMap` is built from
/// this, so the linear scan lives in one place.
val seq_lower_bound
      (#v_T: Type0)
      {| i0: Core_models.Cmp.t_Ord v_T |}
      (s: Rust_primitives.Sequence.t_Seq v_T)
      (key: v_T)
    : Prims.Pure (usize & bool) Prims.l_True (fun _ -> Prims.l_True)

/// `seq_lower_bound` against a *borrowed* key, as std's `BTreeSet`
/// lookups take. Spelled out separately rather than as the general case
/// so that the methods which do not need a `Borrow` bound (`insert`,
/// the set operations, …) do not have to carry one — the model has no
/// blanket `impl<T> Borrow<T> for T`.
val seq_lower_bound_borrowed
      (#v_T #v_Q: Type0)
      {| i0: Core_models.Borrow.t_Borrow v_T v_Q |}
      {| i1: Core_models.Cmp.t_Ord v_T |}
      {| i2: Core_models.Cmp.t_Ord v_Q |}
      (s: Rust_primitives.Sequence.t_Seq v_T)
      (key: v_Q)
    : Prims.Pure (usize & bool) Prims.l_True (fun _ -> Prims.l_True)

/// Insert `value` at `index`, shifting the tail right (see the same
/// helper in `vec_deque`).
val seq_insert (#v_T: Type0) (s: Rust_primitives.Sequence.t_Seq v_T) (index: usize) (value: v_T)
    : Prims.Pure (Rust_primitives.Sequence.t_Seq v_T)
      (requires
        index <=. (Rust_primitives.Sequence.seq_len #v_T s <: usize) &&
        (Rust_primitives.Sequence.seq_len #v_T s <: usize) <. Core_models.Num.impl_usize__MAX)
      (fun _ -> Prims.l_True)
