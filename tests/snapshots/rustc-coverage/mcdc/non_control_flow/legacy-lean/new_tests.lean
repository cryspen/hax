
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


namespace new_tests.rustc_coverage__mcdc__non_control_flow

@[spec]
def assign_and (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a &&? b);
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def assign_or (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a ||? b);
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def assign_3 (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a ||? (← (b &&? c)));
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def assign_3_bis (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← ((← (a &&? b)) ||? c);
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def right_comb_tree (a : Bool) (b : Bool) (c : Bool) (d : Bool) (e : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  let x : Bool ← (a &&? (← (b &&? (← (c &&? (← (d &&? e)))))));
  let _ ← (core_models.hint.black_box Bool x);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def foo (a : Bool) : RustM Bool := do (core_models.hint.black_box Bool a)

@[spec]
def func_call (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (foo (← (a &&? b)));
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (assign_and true false);
  let _ ← (assign_and true true);
  let _ ← (assign_and false false);
  let _ ← (assign_or true false);
  let _ ← (assign_or true true);
  let _ ← (assign_or false false);
  let _ ← (assign_3 true false false);
  let _ ← (assign_3 true true false);
  let _ ← (assign_3 false false true);
  let _ ← (assign_3 false true true);
  let _ ← (assign_3_bis true false false);
  let _ ← (assign_3_bis true true false);
  let _ ← (assign_3_bis false false true);
  let _ ← (assign_3_bis false true true);
  let _ ← (right_comb_tree false false false true true);
  let _ ← (right_comb_tree true false false true true);
  let _ ← (right_comb_tree true true true true true);
  let _ ← (func_call true false);
  let _ ← (func_call true true);
  let _ ← (func_call false false);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__mcdc__non_control_flow

