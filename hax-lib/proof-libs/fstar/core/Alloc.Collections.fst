module Alloc.Collections
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::collections::TryReserveErrorKind`].
/// DEVIATION(std): std's `AllocError` variant carries the
/// `core::alloc::Layout` of the failed request (plus a `#[doc(hidden)]`
/// unit field). We do not model `Layout`, and the model's collections
/// never fail to allocate, so the payload would be unobservable.
type t_TryReserveErrorKind =
  | TryReserveErrorKind_CapacityOverflow : t_TryReserveErrorKind
  | TryReserveErrorKind_AllocError : t_TryReserveErrorKind

let t_TryReserveErrorKind_cast_to_repr (x: t_TryReserveErrorKind) : isize =
  match x <: t_TryReserveErrorKind with
  | TryReserveErrorKind_CapacityOverflow  -> mk_isize 0
  | TryReserveErrorKind_AllocError  -> mk_isize 1

let impl_1: Core_models.Clone.t_Clone t_TryReserveErrorKind =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

/// See [`std::collections::TryReserveError`]: the error returned by the
/// `try_reserve` family. The model never fails to allocate, so no model
/// operation ever produces one.
type t_TryReserveError = | TryReserveError : t_TryReserveErrorKind -> t_TryReserveError

let impl_2: Core_models.Clone.t_Clone t_TryReserveError =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

/// See [`std::collections::TryReserveError::kind`] (unstable in std:
/// `try_reserve_kind`), which returns a clone of the stored kind.
let impl_TryReserveError__kind (self: t_TryReserveError) : t_TryReserveErrorKind =
  Core_models.Clone.f_clone #t_TryReserveErrorKind #FStar.Tactics.Typeclasses.solve self._0
