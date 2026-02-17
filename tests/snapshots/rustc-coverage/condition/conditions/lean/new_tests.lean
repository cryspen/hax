
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


namespace new_tests.rustc_coverage__condition__conditions

def simple_assign (a : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let x : Bool := a;
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

def assign_and (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a &&? b);
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

def assign_or (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a ||? b);
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

def assign_3_or_and (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a ||? (← (b &&? c)));
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

def assign_3_and_or (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← ((← (a &&? b)) ||? c);
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

def foo (a : Bool) : RustM Bool := do (core_models.hint.black_box Bool a)

def func_call (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (foo (← (a &&? b)));
  (pure rust_primitives.hax.Tuple0.mk)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (simple_assign true);
  let _ ← (simple_assign false);
  let _ ← (assign_and true false);
  let _ ← (assign_and true true);
  let _ ← (assign_and false false);
  let _ ← (assign_or true false);
  let _ ← (assign_or true true);
  let _ ← (assign_or false false);
  let _ ← (assign_3_or_and true false false);
  let _ ← (assign_3_or_and true true false);
  let _ ← (assign_3_or_and false false true);
  let _ ← (assign_3_or_and false true true);
  let _ ← (assign_3_and_or true false false);
  let _ ← (assign_3_and_or true true false);
  let _ ← (assign_3_and_or false false true);
  let _ ← (assign_3_and_or false true true);
  let _ ← (func_call true false);
  let _ ← (func_call true true);
  let _ ← (func_call false false);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__condition__conditions

