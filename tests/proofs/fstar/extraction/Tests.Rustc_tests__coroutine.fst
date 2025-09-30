module Tests.Rustc_tests__coroutine
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let get_u32 (v_val: bool) : Core.Result.t_Result u32 Alloc.String.t_String =
  if v_val
  then Core.Result.Result_Ok (mk_u32 1) <: Core.Result.t_Result u32 Alloc.String.t_String
  else
    Core.Result.Result_Err
    (Core.Convert.f_from #Alloc.String.t_String
        #string
        #FStar.Tactics.Typeclasses.solve
        "some error")
    <:
    Core.Result.t_Result u32 Alloc.String.t_String

let main (_: Prims.unit) : Prims.unit =
  Rust_primitives.Hax.failure "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.\nGot type `Coroutine`: coroutines are not supported by hax\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/924.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `AST import`.\n[0m"
    ""
