
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

def Tests.Rustc_tests__coroutine.get_u32
  (val : Bool)
  : Result (Core.Result.Result u32 Alloc.String.String)
  := do
  (← if val then do
    (Core.Result.Result.Ok (1 : u32))
  else do
    (Core.Result.Result.Err (← Core.Convert.From.from "some error")))

def Tests.Rustc_tests__coroutine.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.failure
      "something is not implemented yet.This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Got type `Coroutine`: coroutines are not supported by hax

This is discussed in issue https://github.com/hacspec/hax/issues/924.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `AST import`.
"
      "")