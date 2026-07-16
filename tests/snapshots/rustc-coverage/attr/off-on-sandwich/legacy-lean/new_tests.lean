
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


namespace new_tests.rustc_coverage__attr__off_on_sandwich

@[spec]
def do_stuff (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def dense_a.dense_b.dense_c (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def dense_a.dense_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (dense_a.dense_b.dense_c rust_primitives.hax.Tuple0.mk);
  let _ ← (dense_a.dense_b.dense_c rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def dense_a (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (dense_a.dense_b rust_primitives.hax.Tuple0.mk);
  let _ ← (dense_a.dense_b rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
    (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (do_stuff rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def sparse_a.sparse_b.sparse_c.sparse_d (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
      rust_primitives.hax.Tuple0.mk);
  let _ ←
    (sparse_a.sparse_b.sparse_c.sparse_d.sparse_e
      rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def sparse_a.sparse_b.sparse_c (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (sparse_a.sparse_b.sparse_c.sparse_d rust_primitives.hax.Tuple0.mk);
  let _ ← (sparse_a.sparse_b.sparse_c.sparse_d rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def sparse_a.sparse_b (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (sparse_a.sparse_b.sparse_c rust_primitives.hax.Tuple0.mk);
  let _ ← (sparse_a.sparse_b.sparse_c rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def sparse_a (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (sparse_a.sparse_b rust_primitives.hax.Tuple0.mk);
  let _ ← (sparse_a.sparse_b rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (dense_a rust_primitives.hax.Tuple0.mk);
  let _ ← (sparse_a rust_primitives.hax.Tuple0.mk);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__attr__off_on_sandwich
