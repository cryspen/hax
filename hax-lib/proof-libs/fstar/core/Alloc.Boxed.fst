module Alloc.Boxed
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Box (v_T: Type0) = | Box : v_T -> t_Box v_T

let impl__new (#v_T: Type0) (v: v_T) : v_T = v
