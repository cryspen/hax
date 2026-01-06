import Hax.Core

set_option mvcgen.warning false
open Core.Ops
open Std.Do

namespace Core.Convert

class TryInto (Self: Type) (T: Type) {E: Type} where
  try_into (Self T) : Self → (RustM (Core_models.Result.Result T E))

instance {α : Type} {n : Nat} : TryInto (RustSlice α) (RustArray α n) (E := Core.Array.TryFromSliceError) where
  try_into a :=
   pure (
     if h: a.size = n then
       Core_models.Result.Result.Ok (a.toVector.cast h)
     else
       .Err Core.Array.TryFromSliceError.array.TryFromSliceError
     )

@[spec]
theorem TryInto.try_into.spec {α : Type} {n: Nat} (a: RustSlice α) :
  (h: a.size = n) →
  ⦃ ⌜ True ⌝ ⦄
  (TryInto.try_into (RustSlice α) (RustArray α n) (E := Core.Array.TryFromSliceError) a )
  ⦃ ⇓ r => ⌜ r = .Ok (a.toVector.cast h) ⌝ ⦄ := by
  intro h
  mvcgen [TryInto.try_into]
  grind

end Core.Convert

def Core.Result.Impl.unwrap
  (T : Type) (E : Type) (self : (Core_models.Result.Result T E))
  : RustM T
  := do
  match self with
    | (Core_models.Result.Result.Ok t) => (pure t)
    | (Core_models.Result.Result.Err _)
      => (Core_models.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

@[spec]
theorem Core.Result.Impl.unwrap.spec {α β} (x: Core_models.Result.Result α β) v :
  x = Core_models.Result.Result.Ok v →
  ⦃ ⌜ True ⌝ ⦄
  (Impl.unwrap α β x)
  ⦃ ⇓ r => ⌜ r = v ⌝ ⦄
  := by
  intros
  mvcgen [Impl.unwrap] <;> try grind
