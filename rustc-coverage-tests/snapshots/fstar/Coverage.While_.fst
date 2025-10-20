module Coverage.While_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let num:i32 = mk_i32 9 in
  Rust_primitives.Hax.while_loop (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        true)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        num >=. mk_i32 10 <: bool)
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
    ()
    (fun temp_0_ ->
        let _:Prims.unit = temp_0_ in
        ()),
  ()
  <:
  (Prims.unit & Prims.unit)
