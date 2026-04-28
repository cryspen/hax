module Core_models.Num.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::num::TryFromIntError`]
type t_TryFromIntError = | TryFromIntError : Prims.unit -> t_TryFromIntError

/// See [`std::num::IntErrorKind`]
type t_IntErrorKind = | IntErrorKind : t_IntErrorKind

/// See [`std::num::ParseIntError`]
type t_ParseIntError = { f_kind:t_IntErrorKind }
