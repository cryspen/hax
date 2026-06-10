module New_tests.Legacy__lean_tests__lib.Array
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let f (v_N: usize) (x: t_Array u8 v_N) : Prims.unit = ()

let g (v_N: usize) (x: t_Array u8 v_N) : Prims.unit =
  let _:Prims.unit = f v_N x in
  let _:Prims.unit =
    f (mk_usize 10) (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 10) <: t_Array u8 (mk_usize 10))
  in
  ()
