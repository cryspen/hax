
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


namespace new_tests.rustc_coverage__partial_eq

structure Version where
  major : usize
  minor : usize
  patch : usize

@[instance] opaque Impl_1.AssociatedTypes :
  core_models.clone.Clone.AssociatedTypes Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  core_models.clone.Clone Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  core_models.fmt.Debug.AssociatedTypes Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  core_models.fmt.Debug Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3.AssociatedTypes :
  core_models.marker.StructuralPartialEq.AssociatedTypes Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  core_models.marker.StructuralPartialEq Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  core_models.cmp.PartialEq.AssociatedTypes Version Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  core_models.cmp.PartialEq Version Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  core_models.cmp.Eq.AssociatedTypes Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  core_models.cmp.Eq Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6.AssociatedTypes :
  core_models.cmp.PartialOrd.AssociatedTypes Version Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_6 :
  core_models.cmp.PartialOrd Version Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7.AssociatedTypes :
  core_models.cmp.Ord.AssociatedTypes Version :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_7 :
  core_models.cmp.Ord Version :=
  by constructor <;> exact Inhabited.default

@[spec]
def Impl.new (major : usize) (minor : usize) (patch : usize) :
    RustM Version := do
  (pure (Version.mk (major := major) (minor := minor) (patch := patch)))

--  @fail(extraction): ssprove(HAX0001)
@[spec]
def main (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Tuple0 := do
  let version_3_2_1 : Version ← (Impl.new (3 : usize) (2 : usize) (1 : usize));
  let version_3_3_0 : Version ← (Impl.new (3 : usize) (3 : usize) (0 : usize));
  let args : (rust_primitives.hax.Tuple3 Version Version Bool) :=
    (rust_primitives.hax.Tuple3.mk
      version_3_2_1
      version_3_3_0
      (← (core_models.cmp.PartialOrd.lt
        Version
        Version version_3_2_1 version_3_3_0)));
  let args : (RustArray core_models.fmt.rt.Argument 3) :=
    (RustArray.ofVec #v[(← (core_models.fmt.rt.Impl.new_debug Version
                            (rust_primitives.hax.Tuple3._0 args))),
                          (← (core_models.fmt.rt.Impl.new_debug Version
                            (rust_primitives.hax.Tuple3._1 args))),
                          (← (core_models.fmt.rt.Impl.new_display Bool
                            (rust_primitives.hax.Tuple3._2 args)))]);
  let _ ←
    (std.io.stdio._print
      (← (core_models.fmt.rt.Impl_1.new_v1 ((4 : usize)) ((3 : usize))
        (RustArray.ofVec #v["", " < ", " = ", "\n"])
        args)));
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure rust_primitives.hax.Tuple0.mk)

end new_tests.rustc_coverage__partial_eq

