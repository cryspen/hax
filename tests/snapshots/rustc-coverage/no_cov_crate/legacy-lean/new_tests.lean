
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/legacy-lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace new_tests.rustc_coverage__no_cov_crate

@[spec]
def do_not_add_coverage_1 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called but not covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def do_not_add_coverage_2 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called but not covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def do_not_add_coverage_not_called (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["not called and not covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def add_coverage_1 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called and covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def add_coverage_2 (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called and covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def add_coverage_not_called (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["not called but covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__no_cov_crate


namespace new_tests.rustc_coverage__no_cov_crate.nested_fns

@[spec]
def outer_not_covered.inner (is_true : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if is_true then do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["called and covered\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["absolutely not covered\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer_not_covered (is_true : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called but not covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ← (outer_not_covered.inner is_true);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer.inner_not_covered (is_true : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if is_true then do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["called but not covered\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["absolutely not covered\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer (is_true : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called and covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ← (outer.inner_not_covered is_true);
  (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer_both_covered.inner (is_true : Bool) :
    RustM rust_primitives.hax.Tuple0 := do
  if is_true then do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["called and covered\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)
  else do
    let _ ←
      (std.io.stdio._print
        (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
          (RustArray.ofVec #v["absolutely not covered\n"]))));
    let _ := rust_primitives.hax.Tuple0.mk;
    (pure rust_primitives.hax.Tuple0.mk)

@[spec]
def outer_both_covered (is_true : Bool) : RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize))
        (RustArray.ofVec #v["called and covered\n"]))));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ← (outer_both_covered.inner is_true);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__no_cov_crate.nested_fns


namespace new_tests.rustc_coverage__no_cov_crate

@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let is_true : Bool ←
    ((← (core_models.iter.traits.exact_size.ExactSizeIterator.len
        std.env.Args (← (std.env.args rust_primitives.hax.Tuple0.mk))))
      ==? (1 : usize));
  let _ ← (do_not_add_coverage_1 rust_primitives.hax.Tuple0.mk);
  let _ ← (do_not_add_coverage_2 rust_primitives.hax.Tuple0.mk);
  let _ ← (add_coverage_1 rust_primitives.hax.Tuple0.mk);
  let _ ← (add_coverage_2 rust_primitives.hax.Tuple0.mk);
  let _ ←
    (new_tests.rustc_coverage__no_cov_crate.nested_fns.outer_not_covered
      is_true);
  let _ ← (new_tests.rustc_coverage__no_cov_crate.nested_fns.outer is_true);
  let _ ←
    (new_tests.rustc_coverage__no_cov_crate.nested_fns.outer_both_covered
      is_true);
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__no_cov_crate

