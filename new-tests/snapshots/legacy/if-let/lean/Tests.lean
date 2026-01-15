
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

def Tests.Legacy__if_let.fun_with_if_let
  (_ : Rust_primitives.Hax.Tuple0)
  : Result u8
  := do
  let x : (Core.Option.Option u8) := (Core.Option.Option.Some (5 : u8));
  match x with | (Core.Option.Option.Some x) => (pure x) | _ => (pure (7 : u8))