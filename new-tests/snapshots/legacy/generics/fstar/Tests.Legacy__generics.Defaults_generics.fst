module Tests.Legacy__generics.Defaults_generics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Defaults (v_T: Type0) (v_N: usize) = | Defaults : t_Array v_T v_N -> t_Defaults v_T v_N

let f (_: t_Defaults Prims.unit (mk_usize 2)) : Prims.unit = ()
