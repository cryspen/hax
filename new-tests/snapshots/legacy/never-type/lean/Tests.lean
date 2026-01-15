
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

inductive Tests.Legacy__never_type.False : Type


def Tests.Legacy__never_type.False
  (x : Tests.Legacy__never_type.False)
  : Result Rust_primitives.Hax.Never
  := do
  match x with 

def Tests.Legacy__never_type.never
  (h : Tests.Legacy__never_type.False)
  : Result Rust_primitives.Hax.Never
  := do
  match h with 

def Tests.Legacy__never_type.test (b : Bool) : Result u8 := do
  let _ ←
    if b then
      (Rust_primitives.Hax.never_to_any
        (← (Core.Panicking.panic "explicit panic")))
    else
      (pure Rust_primitives.Hax.Tuple0.mk);
  (pure (3 : u8))

def Tests.Legacy__never_type.any
  (T : Type) (_ : Rust_primitives.Hax.Tuple0)
  : Result T
  := do
  (Rust_primitives.Hax.never_to_any (← (Core.Panicking.panic "explicit panic")))