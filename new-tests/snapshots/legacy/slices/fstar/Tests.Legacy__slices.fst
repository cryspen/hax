module Tests.Legacy__slices
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let v_VERSION: t_Slice u8 =
  (let list = [mk_u8 118; mk_u8 49] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
    Rust_primitives.Hax.array_of_list 2 list)
  <:
  t_Slice u8

let do_something (_: t_Slice u8) : Prims.unit = ()

let r#unsized (_: t_Array (t_Slice u8) (mk_usize 1)) : Prims.unit = ()

let sized (x: t_Array (t_Array u8 (mk_usize 4)) (mk_usize 1)) : Prims.unit =
  r#unsized (let list = [x.[ mk_usize 0 ] <: t_Slice u8] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list)
