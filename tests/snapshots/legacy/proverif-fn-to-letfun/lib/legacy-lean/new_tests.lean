
-- Legacy lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.legacy__proverif_fn_to_letfun__lib

structure A where
  x : usize
  y : u8

structure B where
  b : Bool

@[spec]
def some_function (_ : rust_primitives.hax.Tuple0) : RustM Bool := do
  (pure true)

@[spec]
def some_other_function (b : Bool) : RustM u8 := do (pure (5 : u8))

@[spec]
def longer_function (x : String) : RustM A := do
  let b : Bool ← (some_function rust_primitives.hax.Tuple0.mk);
  let d : u8 ← (some_other_function b);
  (pure (A.mk (x := (12 : usize)) (y := (9 : u8))))

@[spec]
def another_longer_function (_ : rust_primitives.hax.Tuple0) : RustM B := do
  let b : Bool ← (some_function rust_primitives.hax.Tuple0.mk);
  let d : u8 ← (some_other_function b);
  (pure (B.mk (b := false)))

@[spec]
def void_function (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let b : Bool ← (some_function rust_primitives.hax.Tuple0.mk);
  let d : u8 ← (some_other_function b);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.legacy__proverif_fn_to_letfun__lib

