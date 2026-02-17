
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


namespace new_tests.rustc_coverage__issue_83601

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

--  @fail(extraction): ssprove(HAX0001)
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let bar : Foo := (Foo.mk (1 : u32));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk bar (Foo.mk (1 : u32))) with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)));
  let baz : Foo := (Foo.mk (0 : u32));
  let _ ←
    match (rust_primitives.hax.Tuple2.mk baz (Foo.mk (1 : u32))) with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)))));
  let args : (rust_primitives.hax.Tuple1 Foo) :=
    (rust_primitives.hax.Tuple1.mk (Foo.mk (1 : u32)));
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug Foo
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  let args : (rust_primitives.hax.Tuple1 Foo) :=
    (rust_primitives.hax.Tuple1.mk bar);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug Foo
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  let args : (rust_primitives.hax.Tuple1 Foo) :=
    (rust_primitives.hax.Tuple1.mk baz);
  let args : (RustArray core_models.fmt.rt.Argument 1) :=
    #v[(← (core_models.fmt.rt.Impl.new_debug Foo
           (rust_primitives.hax.Tuple1._0 args)))];
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((2 : usize)) ((1 : usize))
        #v["", "
"]
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__issue_83601

