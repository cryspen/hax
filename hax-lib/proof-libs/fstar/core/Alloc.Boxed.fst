module Alloc.Boxed
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

type t_Box (v_T: Type0) (v_A: Type0) =
  | Box : v_T -> Core_models.Option.t_Option v_A -> t_Box v_T v_A

let impl__new (#v_T #v_A: Type0) (v: v_T) : t_Box v_T v_A =
  Box v (Core_models.Option.Option_None <: Core_models.Option.t_Option v_A) <: t_Box v_T v_A
