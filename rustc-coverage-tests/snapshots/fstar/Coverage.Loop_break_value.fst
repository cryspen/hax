module Coverage.Loop_break_value
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : Prims.unit =
  let result:i32 =
    Rust_primitives.Hax.failure "(FunctionalizeLoops) something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/405.\nPlease upvote or comment this issue if you see this error message.\nLoop without mutation"
      "{\n loop {\n core::ops::control_flow::ControlFlow_Break(Tuple2(10, Tuple0()))\n }\n }",
    ()
    <:
    (Prims.unit & Prims.unit)
  in
  ()
