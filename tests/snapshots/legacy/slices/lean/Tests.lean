
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

def Tests.Legacy__slices.VERSION : Result (RustSlice u8) := do
  (← Rust_primitives.unsize #v[(118 : u8), (49 : u8)])

def Tests.Legacy__slices.do_something
  (_ : (RustSlice u8))
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__slices.r#unsized
  (_ : (RustArray (RustSlice u8) (1 : usize)))
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Legacy__slices.sized
  (x : (RustArray (RustArray u8 (4 : usize)) (1 : usize)))
  : Result Rust_primitives.Hax.Tuple0
  := do
  (← Tests.Legacy__slices.r#unsized
      #v[(← Rust_primitives.unsize
               (← Core.Ops.Index.Index.index x (0 : usize)))])