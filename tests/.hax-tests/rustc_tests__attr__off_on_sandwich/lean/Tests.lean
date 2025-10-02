
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

def Tests.Rustc_tests__attr__off_on_sandwich.do_stuff
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.dense_a.dense_b.dense_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.do_stuff
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.dense_a.dense_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.dense_a.dense_b.dense_c
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.dense_a.dense_b.dense_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.dense_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.dense_a.dense_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.dense_a.dense_b
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def
  Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.do_stuff
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c.sparse_d
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b.sparse_c
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.sparse_a
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a.sparse_b
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk

def Tests.Rustc_tests__attr__off_on_sandwich.main
  (_ : Rust_primitives.Hax.Tuple0)
  : Result Rust_primitives.Hax.Tuple0
  := do
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.dense_a
        Rust_primitives.Hax.Tuple0.mk));
  let _ ← (pure
    (← Tests.Rustc_tests__attr__off_on_sandwich.sparse_a
        Rust_primitives.Hax.Tuple0.mk));
  Rust_primitives.Hax.Tuple0.mk