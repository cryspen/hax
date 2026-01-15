
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

inductive Tests.Legacy__unsafe.Impossible : Type


def Tests.Legacy__unsafe.Impossible
  (x : Tests.Legacy__unsafe.Impossible)
  : Result Rust_primitives.Hax.Never
  := do
  match x with 

def Tests.Legacy__unsafe._.requires
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  (pure false)

--  @fail(extraction): ssprove(HAX0008), coq(HAX0008)
def Tests.Legacy__unsafe.impossible
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Tests.Legacy__unsafe.Impossible
  := do
  (Rust_primitives.Hax.never_to_any
    (← (Core.Hint.unreachable_unchecked Rust_primitives.Hax.Tuple0.mk)))

def Tests.Legacy__unsafe.__1.requires
  (slice : (RustSlice u8))
  : Result Bool
  := do
  (Rust_primitives.Hax.Machine_int.gt
    (← (Core.Slice.Impl.len u8 slice))
    (10 : usize))

--  @fail(extraction): ssprove(HAX0008), coq(HAX0008)
def Tests.Legacy__unsafe.get_unchecked_example
  (slice : (RustSlice u8))
  : Result u8
  := do
  (Core.Slice.Impl.get_unchecked u8 usize slice (6 : usize))