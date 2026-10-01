module New_tests.Rustc_coverage__branch__generics
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let print_size (#v_T: Type0) (_: Prims.unit) : Prims.unit =
  if (Core_models.Mem.size_of #v_T () <: usize) >. mk_usize 4
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
            (let list = ["size > 4\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core_models.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()
  else
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
            (let list = ["size <= 4\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core_models.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = print_size #Prims.unit () in
  let _:Prims.unit = print_size #u32 () in
  let _:Prims.unit = print_size #u64 () in
  ()
