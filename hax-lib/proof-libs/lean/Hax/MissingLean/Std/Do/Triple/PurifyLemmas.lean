import Hax.rust_primitives.RustM
import Hax.MissingLean.Std.Do.Triple.Basic
import Hax.Tactic.Purify

open Std.Do
set_option mvcgen.warning false

@[purify]
theorem Purify.dite {α : Type} (c : Prop) [Decidable c]
    (a : c → RustM α) (b : ¬c → RustM α) (pa : c → α) (pb : ¬c → α)
    (ha : ∀ h, ⦃⌜True⌝⦄ a h ⦃⇓ r => ⌜r = pa h⌝⦄)
    (hb : ∀ h, ⦃⌜True⌝⦄ b h ⦃⇓ r => ⌜r = pb h⌝⦄) :
    ⦃⌜True⌝⦄ (dite c a b) ⦃⇓ r => ⌜r = dite c pa pb⌝⦄ := by
  mvcgen [ha, hb] <;> grind
