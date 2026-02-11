
import Hax.Core_models.Extracted

set_option mvcgen.warning false
open rust_primitives.hax
open Core.Ops
open Std.Do

namespace core_models.convert

@[reducible] instance {α : Type} {n : Nat} : TryInto.AssociatedTypes (RustSlice α) (RustArray α n) where
  Error := core_models.array.TryFromSliceError

instance {α : Type} {n : Nat} : TryInto (RustSlice α) (RustArray α n) where
  try_into a :=
   pure (
     if h: a.size = n then
       core_models.result.Result.Ok (a.toVector.cast h)
     else
       .Err core_models.array.TryFromSliceError.mk
     )

@[spec]
theorem TryInto.try_into.spec {α : Type} {n: Nat} (a: RustSlice α) :
  (h: a.size = n) →
  ⦃ ⌜ True ⌝ ⦄
  (TryInto.try_into (RustSlice α) (RustArray α n) a )
  ⦃ ⇓ r => ⌜ r = .Ok (a.toVector.cast h) ⌝ ⦄ := by
  intro h
  mvcgen [TryInto.try_into]
  grind

end core_models.convert
