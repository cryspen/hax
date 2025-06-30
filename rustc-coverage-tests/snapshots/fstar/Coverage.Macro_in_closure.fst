module Coverage.Macro_in_closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_NO_BLOCK:  Prims.unit -> Prims.unit =
  fun temp_0_ ->
    let _:Prims.unit = temp_0_ in
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["hello\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    ()

let v_WITH_BLOCK:  Prims.unit -> Prims.unit =
  fun temp_0_ ->
    let _:Prims.unit = temp_0_ in
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["hello\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = v_NO_BLOCK () in
  let _:Prims.unit = v_WITH_BLOCK () in
  ()
