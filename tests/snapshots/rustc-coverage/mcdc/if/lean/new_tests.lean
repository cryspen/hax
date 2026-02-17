
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


namespace new_tests.rustc_coverage__mcdc__if

def say (message : String) : RustM rust_primitives.hax.Tuple0 := do
  let _ ← (core_models.hint.black_box String message);
  (pure rust_primitives.hax.Tuple0.mk)

def mcdc_check_neither (a : Bool) (b : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? b)) then
    let _ ← (say "a and b");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "not both");
    (pure rust_primitives.hax.Tuple0.mk)

def mcdc_check_a (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? b)) then
    let _ ← (say "a and b");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "not both");
    (pure rust_primitives.hax.Tuple0.mk)

def mcdc_check_b (a : Bool) (b : Bool) : RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? b)) then
    let _ ← (say "a and b");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "not both");
    (pure rust_primitives.hax.Tuple0.mk)

def mcdc_check_both (a : Bool) (b : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? b)) then
    let _ ← (say "a and b");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "not both");
    (pure rust_primitives.hax.Tuple0.mk)

def mcdc_check_tree_decision (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← (a &&? (← (b ||? c)))) then
    let _ ← (say "pass");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "reject");
    (pure rust_primitives.hax.Tuple0.mk)

def mcdc_check_not_tree_decision (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← ((← (a ||? b)) &&? c)) then
    let _ ← (say "pass");
    (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "reject");
    (pure rust_primitives.hax.Tuple0.mk)

def mcdc_nested_if (a : Bool) (b : Bool) (c : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if (← (a ||? b)) then
    let _ ← (say "a or b");
    if (← (b &&? c)) then
      let _ ← (say "b and c");
      (pure rust_primitives.hax.Tuple0.mk)
    else
      (pure rust_primitives.hax.Tuple0.mk)
  else
    let _ ← (say "neither a nor b");
    (pure rust_primitives.hax.Tuple0.mk)

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (mcdc_check_neither false false);
  let _ ← (mcdc_check_neither false true);
  let _ ← (mcdc_check_a true true);
  let _ ← (mcdc_check_a false true);
  let _ ← (mcdc_check_b true true);
  let _ ← (mcdc_check_b true false);
  let _ ← (mcdc_check_both false true);
  let _ ← (mcdc_check_both true true);
  let _ ← (mcdc_check_both true false);
  let _ ← (mcdc_check_tree_decision false true true);
  let _ ← (mcdc_check_tree_decision true true false);
  let _ ← (mcdc_check_tree_decision true false false);
  let _ ← (mcdc_check_tree_decision true false true);
  let _ ← (mcdc_check_not_tree_decision false true true);
  let _ ← (mcdc_check_not_tree_decision true true false);
  let _ ← (mcdc_check_not_tree_decision true false false);
  let _ ← (mcdc_check_not_tree_decision true false true);
  let _ ← (mcdc_nested_if true false true);
  let _ ← (mcdc_nested_if true true true);
  let _ ← (mcdc_nested_if true true false);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__mcdc__if

