module Std.Hash.Random
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_RandomState = | RandomState : t_RandomState
