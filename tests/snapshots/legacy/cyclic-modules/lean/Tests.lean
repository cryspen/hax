
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

def Tests.Legacy__cyclic_modules.Disjoint_cycle_a.g
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cyclic_modules.Disjoint_cycle_b.h
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__cyclic_modules.Disjoint_cycle_a.f
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__cyclic_modules.Disjoint_cycle_b.h
      Rust_primitives.Hax.Tuple0.mk)

def Tests.Legacy__cyclic_modules.Disjoint_cycle_b.i
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__cyclic_modules.Disjoint_cycle_a.g
      Rust_primitives.Hax.Tuple0.mk)