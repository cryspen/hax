module Coverage.While_
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  let num:i32 = mk_i32 9 in
  Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
    "{\n while rust_primitives::hax::machine_int::ge(num, 10) {\n Tuple0\n }\n }",
  ()
  <:
  (Prims.unit & Prims.unit)
