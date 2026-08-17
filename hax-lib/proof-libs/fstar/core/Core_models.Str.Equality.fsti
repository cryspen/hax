module Core_models.Str.Equality
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// `str` compares as its UTF-8 bytes.
[@@ FStar.Tactics.Typeclasses.tcinstance]
val impl:Core_models.Cmp.t_PartialEq string string
