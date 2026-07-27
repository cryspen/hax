module New_tests.Legacy__lean_tests__lib.Specs
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let test (x: u8)
    : Prims.Pure u8
      (requires x >. mk_u8 0)
      (ensures
        fun r ->
          let r:u8 = r in
          r =. x) = x

let test_proof (x: u8)
    : Prims.Pure u8
      (requires x >. mk_u8 0)
      (ensures
        fun r ->
          let r:u8 = r in
          r =. x) = x
