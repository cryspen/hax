module Coverage.Color
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
    "{\n for _i in (core_models::iter::traits::collect::f_into_iter(core_models::ops::range::Range {\n f_start: 0,\n f_end: 0,\n })) {\n Tuple0\n }\n }"
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
