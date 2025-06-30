module Coverage.Color
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
    "{\n for _i in (core::iter::traits::collect::f_into_iter(core::ops::range::Range {\n f_start: 0,\n f_end: 0,\n })) {\n Tuple0\n }\n }"
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
