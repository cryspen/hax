import Hax.CoreModels

set_option mvcgen.warning false
open Rust_primitives.Hax
open Core.Ops
open Std.Do

namespace Core_models.Result

def Impl.unwrap
  (T : Type) (E : Type) (self : (Result T E))
  : RustM T
  := do
  match self with
    | (Result.Ok t) => (pure t)
    | (Result.Err _)
      => (Core_models.Panicking.Internal.panic T Rust_primitives.Hax.Tuple0.mk)

@[spec]
theorem Impl.unwrap.spec {α β} (x: Result α β) v :
  x = Result.Ok v →
  ⦃ ⌜ True ⌝ ⦄
  (Impl.unwrap α β x)
  ⦃ ⇓ r => ⌜ r = v ⌝ ⦄
  := by
  intros
  mvcgen [Impl.unwrap] <;> try grind

end Core_models.Result

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


namespace Core_models.Ops.Function

instance {α β} : FnOnce.AssociatedTypes (α → RustM β) α where
  Output := β

instance {α β} : FnOnce.AssociatedTypes (α → RustM β) (Tuple1 α) where
  Output := β

instance {α β γ} : FnOnce.AssociatedTypes (α → β → RustM γ) (Tuple2 α β) where
  Output := γ

instance {α β} : FnOnce (α → RustM β) α where
  call_once f x := f x

instance {α β} : FnOnce (α → RustM β) (Tuple1 α) where
  call_once f x := f x._0

instance {α β γ : Type} : FnOnce (α → β → RustM γ) (Tuple2 α β) where
  call_once f x := f x._0 x._1

class Fn (Self Args : Type) where
  [_constr1 : outParam (FnOnce.AssociatedTypes Self Args)]
  [_constr2 : (FnOnce Self Args)]
  call (Self Args) : Self -> Args -> RustM (FnOnce.Output Self Args)

instance {α β} [FnOnce.AssociatedTypes (α → RustM β) α] [FnOnce (α → RustM β) α] : Fn (α → RustM β) α where
  call f x := FnOnce.call_once _ _ f x

instance {α β} [FnOnce.AssociatedTypes (α → RustM β) (Tuple1 α)] [FnOnce (α → RustM β) (Tuple1 α)] :
    Fn (α → RustM β) (Tuple1 α) where
  call f x := FnOnce.call_once _ _ f x

instance {α β γ} [FnOnce.AssociatedTypes (α → β → RustM γ) (Tuple2 α β)] [FnOnce (α → β → RustM γ) (Tuple2 α β)] :
    Fn (α → β → RustM γ) (Tuple2 α β) where
  call f x := FnOnce.call_once _ _ f x

end Core_models.Ops.Function
