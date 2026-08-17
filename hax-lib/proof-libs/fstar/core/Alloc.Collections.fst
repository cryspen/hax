module Alloc.Collections
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::collections::TryReserveError`]: the error returned by the
/// `try_reserve*` family. The model's collections never fail to reserve, so
/// it carries no information.
type t_TryReserveError = | TryReserveError : t_TryReserveError
