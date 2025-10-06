
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

def Tests.Legacy__let_else.let_else
  (opt : (Core.Option.Option u32))
  : Result Bool
  := do
  (match opt with | (Core.Option.Option.Some x) => do true | _ => do false)

def Tests.Legacy__let_else.let_else_different_type
  (opt : (Core.Option.Option u32))
  : Result Bool
  := do
  (match opt with
    | (Core.Option.Option.Some x)
      => do
        (← Tests.Legacy__let_else.let_else
            (Core.Option.Option.Some (← x +? (1 : u32))))
    | _ => do false)