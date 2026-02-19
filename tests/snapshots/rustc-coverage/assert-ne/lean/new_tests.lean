
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


namespace new_tests.rustc_coverage__assert_ne

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

def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let _ ←
    match
      (rust_primitives.hax.Tuple2.mk
        (← (core_models.hint.black_box Foo (Foo.mk (5 : u32))))
        (← if (← (core_models.hint.black_box Bool false)) then
          (pure (Foo.mk (0 : u32)))
        else
          (pure (Foo.mk (1 : u32)))))
    with
      | ⟨left_val, right_val⟩ =>
        (hax_lib.assert
          (← (core_models.ops.bit.Not.not
            (← (core_models.cmp.PartialEq.eq Foo Foo left_val right_val)))));
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__assert_ne

