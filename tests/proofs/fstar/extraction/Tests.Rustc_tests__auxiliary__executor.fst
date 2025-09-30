module Tests.Rustc_tests__auxiliary__executor
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

/// Dummy "executor" that just repeatedly polls a future until it's ready.
let block_on
      (#v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Future.Future.t_Future v_F)
      (future: v_F)
    : i0.f_Output =
  Rust_primitives.Hax.failure "The mutation of this [1m&mut[0m is not allowed here.\n\nThis is discussed in issue https://github.com/hacspec/hax/issues/420.\nPlease upvote or comment this issue if you see this error message.[90m\nNote: the error was labeled with context `DirectAndMut`.\n[0m"
    "{\n let mut future: core::pin::t_Pin<&mut F> = {\n {\n let mut pinned: F = { future };\n { unsafe { core::pin::impl_6__new_unchecked::<&mut F>(&mut (pinned)) } }\n }\n };\n {\n let mut context: core::task::wa..."
