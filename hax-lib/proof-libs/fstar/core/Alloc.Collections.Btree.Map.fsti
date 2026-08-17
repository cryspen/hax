module Alloc.Collections.Btree.Map
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::collections::btree_map::UnorderedKeyError`]: the error
/// `CursorMut::insert_before`/`insert_after` return. The cursor API
/// itself is not modeled, so nothing here produces one.
type t_UnorderedKeyError = | UnorderedKeyError : t_UnorderedKeyError
