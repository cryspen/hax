import Hax.Core_models.Extracted

set_option mvcgen.warning false
open rust_primitives.hax
open Core.Ops
open Std.Do

namespace core_models.Result

def Impl.unwrap
  (T : Type) (E : Type) (self : (Result T E))
  : RustM T
  := do
  match self with
    | (Result.Ok t) => (pure t)
    | (Result.Err _)
      => (core_models.Panicking.Internal.panic T rust_primitives.hax.Tuple0.mk)

@[spec]
theorem Impl.unwrap.spec {α β} (x: Result α β) v :
  x = Result.Ok v →
  ⦃ ⌜ True ⌝ ⦄
  (Impl.unwrap α β x)
  ⦃ ⇓ r => ⌜ r = v ⌝ ⦄
  := by
  intros
  mvcgen [Impl.unwrap] <;> try grind

end core_models.Result
