module Tests.Legacy__generics.Assoc_const_param
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

type t_Test (v_N: usize) = | Test : t_Test v_N

let impl__A (v_N: usize) : t_Test v_N = Test <: t_Test v_N

let test (_: Prims.unit) : t_Test (mk_usize 1) = impl__A (mk_usize 1)
