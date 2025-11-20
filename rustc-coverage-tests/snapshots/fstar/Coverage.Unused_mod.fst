module Coverage.Unused_mod
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
          (let list = ["hello world!\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core_models.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  ()
