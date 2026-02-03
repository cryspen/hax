
import Hax.Core_models.Extracted

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
