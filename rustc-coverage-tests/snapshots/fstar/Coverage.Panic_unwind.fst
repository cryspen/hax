module Coverage.Panic_unwind
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let might_panic (should_panic: bool) : Prims.unit =
  if should_panic
  then
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["panicking...\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.Rt.impl_2__new_const (mk_usize
                1)
              (let list = ["panics"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
            <:
            Core.Fmt.t_Arguments)
        <:
        Rust_primitives.Hax.t_Never)
  else
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_2__new_const (mk_usize 1)
            (let list = ["Don't Panic\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()

let main (_: Prims.unit) : Core.Result.t_Result Prims.unit u8 =
  let countdown:i32 = mk_i32 10 in
  let countdown:i32 =
    Rust_primitives.Hax.while_loop (fun countdown ->
          let countdown:i32 = countdown in
          countdown >. mk_i32 0 <: bool)
      (fun countdown ->
          let countdown:i32 = countdown in
          true)
      (fun countdown ->
          let countdown:i32 = countdown in
          Rust_primitives.Hax.Int.from_machine (mk_u32 0) <: Hax_lib.Int.t_Int)
      countdown
      (fun countdown ->
          let countdown:i32 = countdown in
          let _:Prims.unit =
            if countdown =. mk_i32 1
            then
              let _:Prims.unit = might_panic true in
              ()
            else
              if countdown <. mk_i32 5
              then
                let _:Prims.unit = might_panic false in
                ()
          in
          let countdown:i32 = countdown -! mk_i32 1 in
          countdown)
  in
  Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit u8
