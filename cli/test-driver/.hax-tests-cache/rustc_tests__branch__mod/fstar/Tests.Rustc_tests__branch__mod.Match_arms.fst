module Tests.Rustc_tests__branch__mod.Match_arms
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Enum =
  | Enum_A : u32 -> t_Enum
  | Enum_B : u32 -> t_Enum
  | Enum_C : u32 -> t_Enum
  | Enum_D : u32 -> t_Enum

let impl: Core.Clone.t_Clone t_Enum =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Marker.t_Copy t_Enum

unfold
let impl_1 = impl_1'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core.Fmt.t_Debug t_Enum

unfold
let impl_2 = impl_2'

let consume (#v_T: Type0) (x: v_T) : Prims.unit =
  let _:v_T = Core.Hint.black_box #v_T x in
  ()

let match_arms (value: t_Enum) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit =
    match value <: t_Enum with
    | Enum_D d -> consume #u32 d
    | Enum_C c -> consume #u32 c
    | Enum_B b -> consume #u32 b
    | Enum_A a -> consume #u32 a
  in
  let _:Prims.unit = consume #i32 (mk_i32 0) in
  ()

let or_patterns (value: t_Enum) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit =
    match value <: t_Enum with
    | Enum_D x | Enum_C x -> consume #u32 x
    | Enum_B y | Enum_A y -> consume #u32 y
  in
  let _:Prims.unit = consume #i32 (mk_i32 0) in
  ()

let guards (value: t_Enum) (cond: bool) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit =
    match
      (match value <: t_Enum with
        | Enum_D d ->
          (match cond <: bool with
            | true -> Core.Option.Option_Some (consume #u32 d) <: Core.Option.t_Option Prims.unit
            | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
        | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
      <:
      Core.Option.t_Option Prims.unit
    with
    | Core.Option.Option_Some x -> x
    | Core.Option.Option_None  ->
      match
        (match value <: t_Enum with
          | Enum_C c ->
            (match cond <: bool with
              | true -> Core.Option.Option_Some (consume #u32 c) <: Core.Option.t_Option Prims.unit
              | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
          | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
        <:
        Core.Option.t_Option Prims.unit
      with
      | Core.Option.Option_Some x -> x
      | Core.Option.Option_None  ->
        match
          (match value <: t_Enum with
            | Enum_B b ->
              (match cond <: bool with
                | true ->
                  Core.Option.Option_Some (consume #u32 b) <: Core.Option.t_Option Prims.unit
                | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
            | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
          <:
          Core.Option.t_Option Prims.unit
        with
        | Core.Option.Option_Some x -> x
        | Core.Option.Option_None  ->
          match
            (match value <: t_Enum with
              | Enum_A a ->
                (match cond <: bool with
                  | true ->
                    Core.Option.Option_Some (consume #u32 a) <: Core.Option.t_Option Prims.unit
                  | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
              | _ -> Core.Option.Option_None <: Core.Option.t_Option Prims.unit)
            <:
            Core.Option.t_Option Prims.unit
          with
          | Core.Option.Option_Some x -> x
          | Core.Option.Option_None  -> consume #i32 (mk_i32 0)
  in
  let _:Prims.unit = consume #i32 (mk_i32 0) in
  ()

let main__call_everything (e: t_Enum) : (Prims.unit & Prims.unit) =
  let _:Prims.unit = match_arms e in
  let _:Prims.unit = or_patterns e in
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
    "{\n for cond in (core::iter::traits::collect::f_into_iter([false, false, true])) {\n tests::rustc_tests__branch__mod::match_arms::guards(e, cond)\n }\n }"
  ,
  ()
  <:
  (Prims.unit & Prims.unit)

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let _:Prims.unit = main__call_everything (Enum_A (mk_u32 0) <: t_Enum) in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for b in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 2,\n })) {\n tests::rustc_tests__branch__mod::match_arms::main__call_everything(\n tests::rustc_tests_..."

  in
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
      "{\n for c in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 4,\n })) {\n tests::rustc_tests__branch__mod::match_arms::main__call_everything(\n tests::rustc_tests_..."

  in
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
    "{\n for d in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 8,\n })) {\n tests::rustc_tests__branch__mod::match_arms::main__call_everything(\n tests::rustc_tests_..."
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
