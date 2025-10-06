module Tests.Legacy__cyclic_modules.Bundle_enums_a
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_U =
  | U_A : t_U
  | U_B : t_U
  | U_C : Alloc.Vec.t_Vec t_T Alloc.Alloc.t_Global -> t_U

and t_T__from__enums_b =
  | T_A : t_T__from__enums_b
  | T_B : t_T__from__enums_b
  | T_C : Alloc.Vec.t_Vec t_T Alloc.Alloc.t_Global -> t_T__from__enums_b

and t_T =
  | T_A__from__enums_a : t_T
  | T_B__from__enums_a : t_T
  | T_C__from__enums_a : Alloc.Vec.t_Vec t_U Alloc.Alloc.t_Global -> t_T
  | T_D : Alloc.Vec.t_Vec t_T__from__enums_b Alloc.Alloc.t_Global -> t_T

let f (_: Prims.unit) : t_T__from__enums_b = T_A <: t_T__from__enums_b
