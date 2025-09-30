module Tests.Rustc_tests__closure
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : Prims.unit =
  Rust_primitives.Hax.failure "The bindings [\"countdown\"] cannot be mutated here: they don't belong to the closure scope, and this is not allowed.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/1060.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `LocalMutation`.\n[0m"
    "{\n let is_true: bool = {\n rust_primitives::hax::machine_int::eq(\n core::iter::traits::exact_size::f_len(std::env::args(Tuple0)),\n 1,\n )\n };\n {\n let is_false: bool = { core::ops::bit::f_not(is_true) };..."
