module Core_models.Iter.Adapters.Rev
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::iter::Rev`]
type t_Rev (v_I: Type0) = { f_iter:v_I }

let impl__new (#v_I: Type0) (iter: v_I) : t_Rev v_I = { f_iter = iter } <: t_Rev v_I
