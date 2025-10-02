
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

def Tests.Rustc_tests__closure.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Rust_primitives.Hax.failure
      "The bindings ["countdown"] cannot be mutated here: they don't belong to the closure scope, and this is not allowed.

This is discussed in issue https://github.com/hacspec/hax/issues/1060.
Please upvote or comment this issue if you see this error message.
Note: the error was labeled with context `LocalMutation`.
"
      "{
 let is_true: bool = {
 rust_primitives::hax::machine_int::eq(
 core::iter::traits::exact_size::f_len(std::env::args(Tuple0)),
 1,
 )
 };
 {
 let is_false: bool = { core::ops::bit::f_not(is_true) };...")