module Tests.Rustc_tests__branch__if_let
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let say (message: string) : Prims.unit =
  let _:string = Core.Hint.black_box #string message in
  ()

let if_let (input: Core.Option.t_Option string) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit =
    match input <: Core.Option.t_Option string with
    | Core.Option.Option_Some x ->
      let _:Prims.unit = say x in
      ()
    | _ ->
      let _:Prims.unit = say "none" in
      ()
  in
  let _:Prims.unit = say "done" in
  ()

let if_let_chain (a b: Core.Option.t_Option string) : Prims.unit =
  let _:Prims.unit =
    if
      Rust_primitives.Hax.failure "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: `Let` nodes are supposed to be pre-processed\n\n\nNote: the error was labeled with context `AST import`.\n"
        "" &&
      Rust_primitives.Hax.failure "Fatal error: something we considered as impossible occurred! Please report this by submitting an issue on GitHub!\nDetails: `Let` nodes are supposed to be pre-processed\n\n\nNote: the error was labeled with context `AST import`.\n"
        ""
    then
      let _:Prims.unit = say x in
      let _:Prims.unit = say y in
      ()
    else
      let _:Prims.unit = say "not both" in
      ()
  in
  let _:Prims.unit = say "done" in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = if_let (Core.Option.Option_Some "x" <: Core.Option.t_Option string) in
  let _:Prims.unit = if_let (Core.Option.Option_Some "x" <: Core.Option.t_Option string) in
  let _:Prims.unit = if_let (Core.Option.Option_None <: Core.Option.t_Option string) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 8,\n })) {\n tests::rustc_tests__branch__if_let::if_let_chain(\n core::option::Option_Some(\"a\"),\n core..."

  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 4,\n })) {\n tests::rustc_tests__branch__if_let::if_let_chain(\n core::option::Option_Some(\"a\"),\n core..."

  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 2,\n })) {\n tests::rustc_tests__branch__if_let::if_let_chain(\n core::option::Option_None(),\n core::o..."

  in
  let _:Prims.unit =
    if_let_chain (Core.Option.Option_None <: Core.Option.t_Option string)
      (Core.Option.Option_None <: Core.Option.t_Option string)
  in
  ()
