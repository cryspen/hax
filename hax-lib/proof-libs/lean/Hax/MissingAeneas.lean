import Aeneas
import Hax.MissingLean

namespace Aeneas.Std
open Std.Do

abbrev Result.holds (x : Result Prop) : Prop := ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ p => ⌜ p ⌝ ⦄

@[spec]
theorem Result.ok_spec {α : Type} {a : α} {Q} (hQ : (Q.1 a).down) :
  ⦃ ⌜ True ⌝ ⦄ Result.ok a ⦃ Q ⦄ := by simpa [Triple]

@[spec]
theorem Result.fail_spec {α : Type} {e : Error} {Q} (hQ : (Q.2.1 (.up e)).down) :
  ⦃ ⌜ True ⌝ ⦄ (Result.fail e : Result α) ⦃ Q ⦄ := by simpa [Triple]

theorem Result.deterministic (f : Result α) [Inhabited α]:
    ∃ a, ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓?r =>  ⌜ r = a ⌝ ⦄ := by
  match f with
  | .ok a | .fail _ | .div => simp [Triple, WP.wp, PredTrans.apply]

noncomputable def Result.toPure (f : Result α) [Inhabited α] : α :=
  f.deterministic.choose

noncomputable def Result.toPure_spec_mayThrow (f : Result α) [Inhabited α] :
    ⦃ ⌜ True ⌝ ⦄ f ⦃ ⇓?r =>  ⌜ r = f.toPure ⌝ ⦄ :=
  f.deterministic.choose_spec

noncomputable def Result.toPure_spec (f : Result α) [Inhabited α]
    (h : ⦃ P ⦄ f ⦃ Q ⦄) :
    ⦃ P ⦄ f ⦃ (fun r =>  ⌜ r = f.toPure ⌝, Q.2) ⦄ := by
  have := h.and f (toPure_spec_mayThrow f)
  apply Triple.of_entails_right _ (Triple.of_entails_left _ this _)
    <;> simp

attribute [spec] Function.uncurry lift

end Aeneas.Std
