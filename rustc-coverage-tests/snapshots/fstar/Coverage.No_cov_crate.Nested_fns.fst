module Coverage.No_cov_crate.Nested_fns
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let outer_not_covered__inner (is_true: bool) : Prims.unit =
  if is_true
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["called and covered\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()
  else
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["absolutely not covered\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let outer_not_covered (is_true: bool) : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
          (let list = ["called but not covered\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  let _:Prims.unit = outer_not_covered__inner is_true in
  ()

let outer__inner_not_covered (is_true: bool) : Prims.unit =
  if is_true
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["called but not covered\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()
  else
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["absolutely not covered\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let outer (is_true: bool) : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
          (let list = ["called and covered\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  let _:Prims.unit = outer__inner_not_covered is_true in
  ()

let outer_both_covered__inner (is_true: bool) : Prims.unit =
  if is_true
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["called and covered\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()
  else
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["absolutely not covered\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let outer_both_covered (is_true: bool) : Prims.unit =
  let _:Prims.unit =
    Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
          (let list = ["called and covered\n"] in
            FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
            Rust_primitives.Hax.array_of_list 1 list)
        <:
        Core.Fmt.t_Arguments)
  in
  let _:Prims.unit = () in
  let _:Prims.unit = outer_both_covered__inner is_true in
  ()
