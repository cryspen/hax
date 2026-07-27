module New_tests.Legacy__lean_tests__lib.Constants.Const_parameters
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// Function with const parameter
let f (v_N: usize) (_: Prims.unit) : usize = v_N

let v_N0: usize = mk_usize 1

let v_N1: usize = mk_usize 10

let test (_: Prims.unit) : Prims.unit =
  let _:usize = (f (mk_usize 9) () <: usize) +! (f (mk_usize 10) () <: usize) in
  ()

/// Trait definition
class t_T (v_Self: Type0) (v_N_TRAIT: usize) = {
  f_f_pre:v_N_FIELD: usize -> v_Self -> Type0;
  f_f_post:v_N_FIELD: usize -> v_Self -> usize -> Type0;
  f_f:v_N_FIELD: usize -> x0: v_Self
    -> Prims.Pure usize (f_f_pre v_N_FIELD x0) (fun result -> f_f_post v_N_FIELD x0 result)
}

/// Struct definition
type t_S (v_N: usize) = | S : u32 -> t_S v_N

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (v_N_TRAIT: usize) : t_T (t_S v_N_TRAIT) v_N_TRAIT =
  {
    f_f_pre = (fun (v_N_FIELD: usize) (self: t_S v_N_TRAIT) -> true);
    f_f_post = (fun (v_N_FIELD: usize) (self: t_S v_N_TRAIT) (out: usize) -> true);
    f_f = fun (v_N_FIELD: usize) (self: t_S v_N_TRAIT) -> v_N_TRAIT -! v_N_FIELD
  }

let test2
      (v_N2: usize)
      (#v_A: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_T v_A v_N2)
      (x: v_A)
    : usize =
  let s:t_S (mk_usize 10) = S (mk_u32 9) <: t_S (mk_usize 10) in
  let _:usize =
    (f_f #(t_S (mk_usize 10)) #(mk_usize 10) #FStar.Tactics.Typeclasses.solve (mk_usize 1) s
      <:
      usize) +!
    (f_f #v_A #v_N2 #FStar.Tactics.Typeclasses.solve (mk_usize 11) x <: usize)
  in
  let s:t_S (mk_usize 3) = S (mk_u32 9) <: t_S (mk_usize 3) in
  f_f #v_A #v_N2 #FStar.Tactics.Typeclasses.solve (mk_usize 4) x
