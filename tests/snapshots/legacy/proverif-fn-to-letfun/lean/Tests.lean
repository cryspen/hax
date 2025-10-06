
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

structure Tests.Legacy__proverif_fn_to_letfun.A where
  x : usize
  y : u8

structure Tests.Legacy__proverif_fn_to_letfun.B where
  b : Bool

def Tests.Legacy__proverif_fn_to_letfun.some_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Bool
  := do
  true

def Tests.Legacy__proverif_fn_to_letfun.some_other_function
  (b : Bool)
  : Result u8
  := do
  (5 : u8)

def Tests.Legacy__proverif_fn_to_letfun.longer_function
  (x : String)
  : Result Tests.Legacy__proverif_fn_to_letfun.A
  := do
  let b : Bool ← (pure
    (← Tests.Legacy__proverif_fn_to_letfun.some_function
        Rust_primitives.Hax.Tuple0.mk));
  let d : u8 ← (pure
    (← Tests.Legacy__proverif_fn_to_letfun.some_other_function b));
  (Tests.Legacy__proverif_fn_to_letfun.A.mk (x := (12 : usize)) (y := (9 : u8)))

def Tests.Legacy__proverif_fn_to_letfun.another_longer_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Tests.Legacy__proverif_fn_to_letfun.B
  := do
  let b : Bool ← (pure
    (← Tests.Legacy__proverif_fn_to_letfun.some_function
        Rust_primitives.Hax.Tuple0.mk));
  let d : u8 ← (pure
    (← Tests.Legacy__proverif_fn_to_letfun.some_other_function b));
  (Tests.Legacy__proverif_fn_to_letfun.B.mk (b := false))

def Tests.Legacy__proverif_fn_to_letfun.void_function
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let b : Bool ← (pure
    (← Tests.Legacy__proverif_fn_to_letfun.some_function
        Rust_primitives.Hax.Tuple0.mk));
  let d : u8 ← (pure
    (← Tests.Legacy__proverif_fn_to_letfun.some_other_function b));
  Rust_primitives.Hax.Tuple0.mk