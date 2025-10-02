module Tests.Rustc_tests__branch__let_else
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let say (message: string) : Prims.unit =
  let _:string = Core.Hint.black_box #string message in
  ()

let let_else (value: Core.Option.t_Option string) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  match value <: Core.Option.t_Option string with
  | Core.Option.Option_Some x ->
    let _:Prims.unit = say x in
    ()
  | _ ->
    let _:Prims.unit = say "none" in
    ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = let_else (Core.Option.Option_Some "x" <: Core.Option.t_Option string) in
  let _:Prims.unit = let_else (Core.Option.Option_Some "x" <: Core.Option.t_Option string) in
  let _:Prims.unit = let_else (Core.Option.Option_None <: Core.Option.t_Option string) in
  ()
