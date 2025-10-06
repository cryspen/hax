
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

def Tests.Legacy__cyclic_modules.M2.d
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cyclic_modules.M2.c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cyclic_modules.M1.a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__cyclic_modules.M2.c Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__cyclic_modules.M2.b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Legacy__cyclic_modules.M1.a Rust_primitives.Hax.Tuple0.mk));
  (← Tests.Legacy__cyclic_modules.M2.d Rust_primitives.Hax.Tuple0.mk)