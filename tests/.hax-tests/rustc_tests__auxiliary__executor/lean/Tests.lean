
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

def Tests.Rustc_tests__auxiliary__executor.block_on
  (F : Type) [(Core.Future.Future.Future F)] (future : F)
  : Result TODO_LINE_701
  := do
  (← Rust_primitives.Hax.failure
      "The mutation of this &mut is not allowed here.

This is discussed in issue https://github.com/hacspec/hax/issues/420.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `DirectAndMut`.
"
      "{
 let mut future: core::pin::t_Pin<&mut F> = {
 {
 let mut pinned: F = { future };
 { unsafe { core::pin::impl_6__new_unchecked::<&mut F>(&mut (pinned)) } }
 }
 };
 {
 let mut context: core::task::wa...")