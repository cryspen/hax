module Core_models.Iter.Adapters.Rev
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Rust_primitives

/// See [`std::iter::Rev`]
type t_Rev (v_I: Type0) = { f_iter:v_I }
