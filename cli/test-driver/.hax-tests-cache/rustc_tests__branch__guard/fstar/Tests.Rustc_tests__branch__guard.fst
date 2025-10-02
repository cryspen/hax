module Tests.Rustc_tests__branch__guard
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let branch_match_guard (x: Core.Option.t_Option u32) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  match x <: Core.Option.t_Option u32 with
  | Core.Option.Option_Some (Rust_primitives.Integers.MkInt 0) ->
    let _:Prims.unit =
      Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
            (let list = ["zero\n"] in
              FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
              Rust_primitives.Hax.array_of_list 1 list)
          <:
          Core.Fmt.t_Arguments)
    in
    let _:Prims.unit = () in
    ()
  | _ ->
    match
      (match x <: Core.Option.t_Option u32 with
        | Core.Option.Option_Some x ->
          (match (x %! mk_u32 2 <: u32) =. mk_u32 0 <: bool with
            | true ->
              let _:Prims.unit =
                Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                      (let list = ["is nonzero and even\n"] in
                        FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                        Rust_primitives.Hax.array_of_list 1 list)
                    <:
                    Core.Fmt.t_Arguments)
              in
              let _:Prims.unit = () in
              Core.Option.Option_Some () <: Core.Option.t_Option Prims.unit
            | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
        | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
      <:
      Core.Option.t_Option Prims.unit
    with
    | Core.Option.Option_Some x -> x
    | Core.Option.Option_None  ->
      match
        (match x <: Core.Option.t_Option u32 with
          | Core.Option.Option_Some x ->
            (match (x %! mk_u32 3 <: u32) =. mk_u32 0 <: bool with
              | true ->
                let _:Prims.unit =
                  Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                        (let list = ["is nonzero and odd, but divisible by 3\n"] in
                          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                          Rust_primitives.Hax.array_of_list 1 list)
                      <:
                      Core.Fmt.t_Arguments)
                in
                let _:Prims.unit = () in
                Core.Option.Option_Some () <: Core.Option.t_Option Prims.unit
              | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
          | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
        <:
        Core.Option.t_Option Prims.unit
      with
      | Core.Option.Option_Some x -> x
      | Core.Option.Option_None  ->
        let _:Prims.unit =
          Std.Io.Stdio.e_print (Core.Fmt.Rt.impl_1__new_const (mk_usize 1)
                (let list = ["something else\n"] in
                  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                  Rust_primitives.Hax.array_of_list 1 list)
              <:
              Core.Fmt.t_Arguments)
        in
        let _:Prims.unit = () in
        ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit =
    branch_match_guard (Core.Option.Option_Some (mk_u32 0) <: Core.Option.t_Option u32)
  in
  let _:Prims.unit =
    branch_match_guard (Core.Option.Option_Some (mk_u32 2) <: Core.Option.t_Option u32)
  in
  let _:Prims.unit =
    branch_match_guard (Core.Option.Option_Some (mk_u32 6) <: Core.Option.t_Option u32)
  in
  let _:Prims.unit =
    branch_match_guard (Core.Option.Option_Some (mk_u32 3) <: Core.Option.t_Option u32)
  in
  ()
