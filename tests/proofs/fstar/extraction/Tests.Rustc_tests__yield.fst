module Tests.Rustc_tests__yield
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let main (_: Prims.unit) : Prims.unit =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `AST import`.\n[0m"
    ""
