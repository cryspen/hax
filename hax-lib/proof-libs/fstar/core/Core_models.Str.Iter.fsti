module Core_models.Str.Iter
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Split (v_T: Type0) = | Split : v_T -> t_Split v_T
