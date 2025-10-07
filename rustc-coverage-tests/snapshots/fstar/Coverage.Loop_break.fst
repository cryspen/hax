module Coverage.Loop_break
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : (Prims.unit & Prims.unit) =
  Rust_primitives.Hax.failure "something is not implemented yet.\nUnhandled loop kind\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/933.\nPlease upvote or comment this issue if you see this error message.\nNote: the error was labeled with context `FunctionalizeLoops`.\n"
    "{\n loop {\n (if core::hint::black_box::<bool>(true) {\n core::ops::control_flow::ControlFlow_Break(Tuple2(Tuple0, Tuple0()))\n } else {\n core::ops::control_flow::ControlFlow_Continue(Tuple0)\n })\n }\n }"
  ,
  ()
  <:
  (Prims.unit & Prims.unit)
