import Aeneas
import CoreModels
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

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do

namespace Hax

/-! ## Loop-over-range specs

`loop`-over-`core.ops.range.Range` characterisations (the Aeneas encoding of a Rust
`for i in s..e` loop): one for signed index types (`IScalar ty`, `.val : Int`) and one
for the unsigned `Usize` index type (`.val : Nat`). Each takes the loop body and its
per-step contract abstractly, so it never mentions the iterator `Step` dictionary. These
belong in Aeneas proper; they live here until they can be upstreamed. -/

section loop_range_helpers

abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

variable {α : Type}

theorem triple_noThrow_elim {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PredTrans.apply] using h

theorem triple_noThrow_exists_ok {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail e, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

theorem triple_of_ok {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, hp, PredTrans.apply]

end loop_range_helpers

/-- Loop-over-range spec, signed index type (`IScalar ty`, `.val : Int`). The proof
inducts on the number of remaining steps `(e.val - start.val).toNat`. -/
theorem loop_range_spec {ty : IScalarTy} {β : Type}
    (body : (core.ops.range.Range (IScalar ty) × β) →
      Result (ControlFlow (core.ops.range.Range (IScalar ty) × β) β))
    (init : β) (s e : IScalar ty) (inv : IScalar ty → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : IScalar ty), s.val ≤ i.val → i.val ≤ e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ i.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = i.val + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  suffices gen : ∀ (n : Nat) (acc : β) (start : IScalar ty),
    (e.val - start.val).toNat = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok hs
    have hpost := triple_noThrow_elim hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok hs
    have hpost := triple_noThrow_elim hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

set_option maxHeartbeats 2000000 in
/-- Loop-over-range spec, unsigned `Usize` index type (`.val : Nat`). The proof inducts
on the number of remaining steps `e.val - start.val`. -/
theorem loop_range_spec_unsigned {β : Type}
    (body : (core.ops.range.Range Usize × β) →
      Result (ControlFlow (core.ops.range.Range Usize × β) β))
    (init : β) (s e : Usize) (inv : Usize → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Usize), s.val ≤ i.val → i.val ≤ e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body ({ start := i, «end» := e }, acc)
      ⦃ ⇓ r => match r with
        | .cont (iter', acc') =>
          ⌜ i.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = i.val + 1
            ∧ (inv iter'.start acc').holds ⌝
        | .done y => ⌜ (inv e y).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    loop body ({ start := s, «end» := e }, init)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  suffices gen : ∀ (n : Nat) (acc : β) (start : Usize),
    e.val - start.val = n →
    s.val ≤ start.val → start.val ≤ e.val →
    (inv start acc).holds →
    ⦃ ⌜ True ⌝ ⦄ loop body ({ start := start, «end» := e }, acc)
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ by
    exact gen _ init s rfl (Nat.le_refl _) h_le h_init
  intro n
  induction n with
  | zero =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok hs
    have hpost := triple_noThrow_elim hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .cont (iter', acc') =>
      simp at hpost; exact absurd hpost.1 (by omega)
    | .done y =>
      simp at hpost; exact triple_of_ok rfl hpost
  | succ n ih =>
    intro acc start hn hs_le hse_le hinv
    have hs := h_step acc start hs_le hse_le hinv
    obtain ⟨r, hbody⟩ := triple_noThrow_exists_ok hs
    have hpost := triple_noThrow_elim hs hbody
    rw [loop.eq_def, hbody]
    match r with
    | .done y =>
      simp at hpost; exact triple_of_ok rfl hpost
    | .cont (iter', acc') =>
      simp at hpost
      obtain ⟨hlt, hend, hstart, hinv'⟩ := hpost
      have hiter : iter' = { start := iter'.start, «end» := e } := by
        cases iter'; cases hend; rfl
      rw [hiter]
      exact ih acc' iter'.start
        (by rw [hstart]; omega) (by rw [hstart]; omega) (by rw [hstart]; omega) hinv'

end Hax
