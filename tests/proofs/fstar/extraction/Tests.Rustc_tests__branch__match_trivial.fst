module Tests.Rustc_tests__branch__match_trivial
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Uninhabited =

let t_Uninhabited_cast_to_repr (x: t_Uninhabited) : Rust_primitives.Hax.t_Never =
  match x <: t_Uninhabited with

type t_Trivial = | Trivial_Value : t_Trivial

let t_Trivial_cast_to_repr (x: t_Trivial) : isize =
  match x <: t_Trivial with | Trivial_Value  -> mk_isize 0

let consume (#v_T: Type0) (x: v_T) : Prims.unit =
  let _:v_T = Core.Hint.black_box #v_T x in
  ()

let e_uninhabited (x: t_Uninhabited) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit = Rust_primitives.Hax.never_to_any (match x <: t_Uninhabited with ) in
  Rust_primitives.Hax.never_to_any (consume #string "done" <: Prims.unit)

let trivial (x: t_Trivial) : Prims.unit =
  let _:Prims.unit =
    Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `FunctionalizeLoops`.\n[0m"
      "{\n for _ in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 1,\n })) {\n Tuple0\n }\n }"

  in
  let _:Prims.unit = match x <: t_Trivial with | Trivial_Value  -> consume #string "trivial" in
  let _:Prims.unit = consume #string "done" in
  ()

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = trivial (Trivial_Value <: t_Trivial) in
  ()
