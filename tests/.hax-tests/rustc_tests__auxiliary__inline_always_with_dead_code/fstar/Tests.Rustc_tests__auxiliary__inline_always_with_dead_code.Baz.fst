module Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Baz
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let call_me (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = Tests.Rustc_tests__auxiliary__inline_always_with_dead_code.Foo.called () in
  ()
