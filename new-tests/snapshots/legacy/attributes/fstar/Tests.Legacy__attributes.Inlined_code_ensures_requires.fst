module Tests.Legacy__attributes.Inlined_code_ensures_requires
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let increment_array (v: t_Array u8 (mk_usize 4))
    : Prims.Pure (t_Array u8 (mk_usize 4))
      (requires forall i. FStar.Seq.index v i <. mk_u8 254)
      (ensures
        fun vv_future ->
          let vv_future:t_Array u8 (mk_usize 4) = vv_future in
          let future_v:t_Array u8 (mk_usize 4) = vv_future in
          forall i. FStar.Seq.index future_v i >. mk_u8 0) =
  let v:t_Array u8 (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
      (mk_usize 0)
      ((v.[ mk_usize 0 ] <: u8) +! mk_u8 1 <: u8)
  in
  let v:t_Array u8 (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
      (mk_usize 1)
      ((v.[ mk_usize 1 ] <: u8) +! mk_u8 1 <: u8)
  in
  let v:t_Array u8 (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
      (mk_usize 2)
      ((v.[ mk_usize 2 ] <: u8) +! mk_u8 1 <: u8)
  in
  let v:t_Array u8 (mk_usize 4) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize v
      (mk_usize 3)
      ((v.[ mk_usize 3 ] <: u8) +! mk_u8 1 <: u8)
  in
  v
