module Tests.Legacy__attributes.Ensures_on_arity_zero_fns
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let doing_nothing (_: Prims.unit)
    : Prims.Pure Prims.unit
      (requires true)
      (ensures
        fun e_x ->
          let e_x:Prims.unit = e_x in
          true) = ()

let basically_a_constant (_: Prims.unit)
    : Prims.Pure u8
      (requires true)
      (ensures
        fun x ->
          let x:u8 = x in
          x >. mk_u8 100) = mk_u8 127
