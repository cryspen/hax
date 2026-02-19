
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


namespace new_tests.rustc_coverage__bad_counter_ids

structure Foo where
  _0 : u32

@[instance] opaque Impl.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  core_models.fmt.Debug Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.marker.StructuralPartialEq Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Foo Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.cmp.PartialEq Foo Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes Foo :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.cmp.Eq Foo :=
  by constructor <;> exact Inhabited.default

def eq_good (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["a
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)));
  (pure rust_primitives.hax.Tuple0.mk)

def eq_good_message (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["b
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)));
  (pure rust_primitives.hax.Tuple0.mk)

def ne_good (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["c
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)))));
  (pure rust_primitives.hax.Tuple0.mk)

def ne_good_message (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["d
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)))));
  (pure rust_primitives.hax.Tuple0.mk)

def eq_bad (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["e
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)));
  (pure rust_primitives.hax.Tuple0.mk)

def eq_bad_message (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["f
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (3 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)));
  (pure rust_primitives.hax.Tuple0.mk)

def ne_bad (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["g
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)))));
  (pure rust_primitives.hax.Tuple0.mk)

def ne_bad_message (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_const ((1 : usize)) #v["h
"])));
  let _ := rust_primitives.hax.Tuple0.mk;
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk (Foo.mk (1 : u32)) (Foo.mk (1 : u32)))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)))));
  (pure rust_primitives.hax.Tuple0.mk)

--  @fail(extraction): coq(HAX0008, HAX0008, HAX0008, HAX0008), proverif(HAX0008, HAX0008, HAX0008, HAX0008), ssprove(HAX0008, HAX0008, HAX0008, HAX0008)
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ← (eq_good rust_primitives.hax.Tuple0.mk);
  let _ ← (eq_good_message rust_primitives.hax.Tuple0.mk);
  let _ ← (ne_good rust_primitives.hax.Tuple0.mk);
  let _ ← (ne_good_message rust_primitives.hax.Tuple0.mk);
  let _ ←
    (hax_lib.assert
      (← (core_models.result.Impl.is_err rust_primitives.hax.Tuple0 sorry
        (← (std.panic.catch_unwind
          (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
          rust_primitives.hax.Tuple0 eq_bad)))));
  let _ ←
    (hax_lib.assert
      (← (core_models.result.Impl.is_err rust_primitives.hax.Tuple0 sorry
        (← (std.panic.catch_unwind
          (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
          rust_primitives.hax.Tuple0 eq_bad_message)))));
  let _ ←
    (hax_lib.assert
      (← (core_models.result.Impl.is_err rust_primitives.hax.Tuple0 sorry
        (← (std.panic.catch_unwind
          (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
          rust_primitives.hax.Tuple0 ne_bad)))));
  let _ ←
    (hax_lib.assert
      (← (core_models.result.Impl.is_err rust_primitives.hax.Tuple0 sorry
        (← (std.panic.catch_unwind
          (rust_primitives.hax.Tuple0 -> RustM rust_primitives.hax.Tuple0)
          rust_primitives.hax.Tuple0 ne_bad_message)))));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__bad_counter_ids

