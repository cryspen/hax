import Std.Do
import Hax.Rust_primitives.RustM

open Std.Do

/-

# Specs

-/

structure Spec {α}
    (requires : RustM Prop)
    (ensures : α → RustM Prop)
    (f : RustM α) where
  pureRequires : {p : Prop // ⦃ ⌜ True ⌝ ⦄ requires ⦃ ⇓r => ⌜ r = p ⌝ ⦄}
  pureEnsures : {p : α → Prop // pureRequires.val → ∀ a, ⦃ ⌜ True ⌝ ⦄ ensures a ⦃ ⇓r => ⌜ r = p a ⌝ ⦄}
  contract : ⦃ ⌜ pureRequires.val ⌝ ⦄ f ⦃ ⇓r => ⌜ pureEnsures.val r ⌝ ⦄
