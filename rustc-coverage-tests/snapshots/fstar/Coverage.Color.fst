module Coverage.Color
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  Rust_primitives.Hax.Folds.fold_range (mk_i32 0)
    (mk_i32 0)
    (fun temp_0_ temp_1_ ->
        let _:Prims.unit = temp_0_ in
        let _:i32 = temp_1_ in
        true)
    ()
    (fun temp_0_ e_i ->
        let _:Prims.unit = temp_0_ in
        let e_i:i32 = e_i in
        ()),
  ()
  <:
  (Prims.unit & Prims.unit)
