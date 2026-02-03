
import Hax.Core_models.Extracted

set_option mvcgen.warning false
open Rust_primitives.Hax
open Core.Ops
open Std.Do

namespace Core_models.Convert

@[reducible] instance {α : Type} {n : Nat} : TryInto.AssociatedTypes (RustSlice α) (RustArray α n) where
  Error := Core_models.Array.TryFromSliceError

instance {α : Type} {n : Nat} : TryInto (RustSlice α) (RustArray α n) where
  try_into a :=
   pure (
     if h: a.size = n then
       Core_models.Result.Result.Ok (a.toVector.cast h)
     else
       .Err Core_models.Array.TryFromSliceError.array.TryFromSliceError
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

end Core_models.Convert
