module Core_models.Num.Error
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_TryFromIntError = | TryFromIntError : Prims.unit -> t_TryFromIntError

type t_IntErrorKind = | IntErrorKind : t_IntErrorKind

type t_ParseIntError = { f_kind:t_IntErrorKind }
