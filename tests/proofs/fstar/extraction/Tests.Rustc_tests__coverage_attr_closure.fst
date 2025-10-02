module Tests.Rustc_tests__coverage_attr_closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_GLOBAL_CLOSURE_ON:  string -> Prims.unit =
  fun input ->
    let input:string = input in
    let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
      let list = [Core.Fmt.Rt.impl__new_display #string input] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list
    in
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
            (mk_usize 1)
            (let list = [""; "\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
            args
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let v_GLOBAL_CLOSURE_OFF:  string -> Prims.unit =
  fun input ->
    let input:string = input in
    let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
      let list = [Core.Fmt.Rt.impl__new_display #string input] in
      FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
      Rust_primitives.Hax.array_of_list 1 list
    in
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
            (mk_usize 1)
            (let list = [""; "\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
              Rust_primitives.Hax.array_of_list 2 list)
            args
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let contains_closures_on (_: Prims.unit) : Prims.unit =
  let e_local_closure_on: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core.Fmt.Rt.impl__new_display #string input] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  let e_local_closure_off: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core.Fmt.Rt.impl__new_display #string input] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  ()

let contains_closures_off (_: Prims.unit) : Prims.unit =
  let e_local_closure_on: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core.Fmt.Rt.impl__new_display #string input] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  let e_local_closure_off: string -> Prims.unit =
    fun input ->
      let input:string = input in
      let args:t_Array Core.Fmt.Rt.t_Argument (mk_usize 1) =
        let list = [Core.Fmt.Rt.impl__new_display #string input] in
        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
        Rust_primitives.Hax.array_of_list 1 list
      in
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_v1 (mk_usize 2)
              (mk_usize 1)
              (let list = [""; "\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                Rust_primitives.Hax.array_of_list 2 list)
              args
            <:
            Core.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = contains_closures_on () in
  let _:Prims.unit = contains_closures_off () in
  ()
