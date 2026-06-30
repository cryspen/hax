import LoopEquivalence.Extraction.Funs
import Hax
import Lean
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace loop_equivalence

/-! ## Iterator spec -/

@[spec]
theorem IteratorRange_next_spec (i e : Usize) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : Usize), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
  by_cases h : i.val < e.val
  · -- i < e: partial_cmp returns Less, forward_checked succeeds.
    have h_lt' := h_lt h
    simp_all [compare, compareOfLessAndEq,
      core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
      core.Usize.Insts.CoreCloneClone.clone]
    -- `forward_checked` produces `some s` with `s.val = i.val + 1`.
    have hbnd : i.val + (1#usize).val ≤ Usize.max := by scalar_tac
    have hno_ovf := UScalar.overflowing_add_eq i (1#usize)
    have hi1_le : ¬ (i.val + (1#usize).val > UScalar.max .Usize) := by scalar_tac
    simp only [hi1_le, if_false] at hno_ovf
    obtain ⟨hsv, hovf⟩ := hno_ovf
    simp only [core.Usize.Insts.CoreIterRangeStep.forward_checked,
      core.convert.TryFromUTInfallible.Blanket.try_from,
      core.convert.From.Blanket.from,
      core.num.Usize.checked_add, core.num.Usize.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_usize]
    mvcgen
    generalize hov : UScalar.overflowing_add i (1#usize) = ov at *
    obtain ⟨result, overflowed⟩ := ov
    subst hovf
    exact h_lt' _ (by simpa using hsv)
  · -- i ≥ e: partial_cmp returns Equal or Greater (not Less).
    have hle := Nat.le_of_not_lt h
    have h_ge' := h_ge hle
    simp_all [compare, compareOfLessAndEq,
      core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd]
    mvcgen
    all_goals first
      | exact h_ge'
      | (rename_i hlt
         split at hlt <;> rename_i heq <;> split at heq <;>
           (try simp_all); (rename_i heq2; split at heq2 <;> cases heq2))

/-! ## Loop-over-range spec

Specialized to `loop` over `core.ops.range.Range Usize` (the Aeneas encoding
of Rust `for i in s..e` loops). -/

section loop_range_helpers

private abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

private theorem triple_noThrow_elim {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp] using h

private theorem triple_noThrow_exists_ok {x : Result α} {Q : α → Assertion ResultPS}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail e, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

private theorem triple_of_ok {x : Result α} {v : α} {P : α → Prop}
    (hx : x = ok v) (hp : P v) :
    (⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) := by
  subst hx; simp [Triple, WP.wp, hp, PredTrans.apply]

private theorem usize_add_one_toNat (x : USize) (h : x.toNat + 1 < USize.size) :
    (USize.add x 1).toNat = x.toNat + 1 := by
  show (USize.add x 1).toBitVec.toNat = x.toBitVec.toNat + 1
  simp [USize.add, USize.size] at *
  exact Nat.mod_eq_of_lt h

end loop_range_helpers

set_option maxHeartbeats 2000000 in
theorem loop_range_spec {β : Type}
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
  -- Generalize over the current iteration's `start` and induct on the number
  -- of remaining steps `n = e.val - start.val`.
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

/-! ## `for`-loop-with-invariant spec

The definition `Hax.forLoopWithInvariant` and the tactic `for_loop_with_invariant`
that rewrites a raw `loop _ _` into this form live in `Hax.Tactic.ForLoopWithInvariant`. -/

@[spec]
theorem forLoopWithInvariant_spec {β : Type}
    (body : Usize → β → Result β)
    (init : β) (s e : Usize) (inv : Usize → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : Usize), s.val ≤ i.val → i.val < e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body i acc
      ⦃ ⇓ r => ⌜ ∀ (i' : Usize), i'.val = i.val + 1 → (inv i' r).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    Hax.forLoopWithInvariant inv body { start := s, «end» := e } init
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  unfold Hax.forLoopWithInvariant
  apply loop_range_spec _ init s e inv h_le h_init
  intro acc i hsi hie hinv
  unfold core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
    core.IteratorRange.next core.Usize.Insts.CoreIterRangeStep
  by_cases hlt : i.val < e.val
  · -- i < e: `next` yields `(some i, iter')` with `iter'.start.val = i.val + 1`,
    -- then `body i acc` yields the next accumulator.
    have hbody := h_step acc i hsi hlt hinv
    obtain ⟨r, hbody_eq⟩ := triple_noThrow_exists_ok hbody
    have hpost := triple_noThrow_elim hbody hbody_eq
    simp at hpost
    have hbnd : i.val + (1#usize).val ≤ Usize.max := by scalar_tac
    have hno_ovf := UScalar.overflowing_add_eq i (1#usize)
    have hi1_le : ¬ (i.val + (1#usize).val > UScalar.max .Usize) := by scalar_tac
    simp only [hi1_le, if_false] at hno_ovf
    obtain ⟨hsv, hovf⟩ := hno_ovf
    simp only [Triple, PredTrans.apply, wp, core.Usize.Insts.CoreCmpPartialOrdUsize,
      core.mkUPartialOrd, compare, compareOfLessAndEq, hlt, ↓reduceIte,
      core.Usize.Insts.CoreCloneClone.clone, core.Usize.Insts.CoreIterRangeStep.forward_checked,
      core.convert.TryFromUTInfallible.Blanket.try_from, core.convert.From.Blanket.from, bind_tc_ok,
      core.num.Usize.checked_add, core.num.Usize.overflowing_add,
      rust_primitives.arithmetic.overflowing_add_usize, bind_assoc, holds, ExceptConds.fst_false,
      ExceptConds.snd_false, SPred.entails_nil, SPred.down_pure, forall_const, true_and]
    generalize hov : UScalar.overflowing_add i (1#usize) = ov at *
    obtain ⟨i', overflowed⟩ := ov
    simp at hsv hovf
    subst hovf
    have hi'val' : i'.val = i.val + 1 := by simpa using hsv
    have hh : (inv i' r).holds := hpost i' hi'val'
    simp [Triple, WP.wp, Result.holds, PredTrans.apply, hbody_eq] at hh ⊢
    refine ⟨hi'val', ?_⟩
    rcases hires : inv i' r with _ | _ | _ <;> simp [hires] at hh ⊢; exact hh
  · -- i ≥ e: combined with `hie`, `i = e`. `next` yields `(none, _)`, body short-circuits.
    have hieq : i.val = e.val := Nat.le_antisymm hie (Nat.le_of_not_lt hlt)
    have hi_eq_e : i = e := UScalar.eq_imp _ _ hieq
    have hh : (inv e acc).holds := by rw [← hi_eq_e]; exact hinv
    simp [compare, compareOfLessAndEq, hi_eq_e,
          core.Usize.Insts.CoreCmpPartialOrdUsize, core.mkUPartialOrd,
          Triple, WP.wp, Result.holds] at hh ⊢
    exact hh

-- Local automation configuration
attribute [local spec] g f op g_loop g_loop.body f_loop f_loop.body g_loop_inv f_loop_inv g_post
attribute [local spec] core.Array.Insts.CoreCloneClone.clone

set_option maxHeartbeats 1000000
theorem g_spec {N : Usize} (arr : Array U64 N) :
    ⦃ ⌜ True ⌝ ⦄
    g arr
    ⦃ ⇓ future_arr => ⌜(do let x ← f arr; pure (future_arr == x) : Result Bool).holds ⌝ ⦄ := by
  unfold g g_loop g_loop.body f f_loop f_loop.body
  for_loop_with_invariant
    fun i r =>
      pure
        (∀ (j : Usize),
          (do
              let a ← g_loop_inv r arr i j
              pure (a = true)).holds)
  for_loop_with_invariant
    fun i r =>
      pure
        (∀ (j : Usize),
          (do
              let a ← f_loop_inv r arr i j
              pure (a = true)).holds)
  hax_mvcgen
  all_goals try grind
  · -- [g] loop step (j < i'): g_loop_inv branch 1.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply h_19 j <;> grind [UScalar.ofNatCore_val_eq ]
  · -- [g] loop step (¬j < i' ∧ j < N): g_loop_inv branch 2.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply h_19 j <;> grind
  · -- [f] loop step in N%2>0 branch (j < i'): f_loop_inv branch 1.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply h_21 j <;> grind
  · -- [f] loop step in N%2>0 branch (¬j < i' ∧ j < N): f_loop_inv branch 2.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply h_22 j <;> grind
  · -- N%2>0 post: g's update at N-1 vs f_loop's full result.
    simp at *; try subst_vars
    apply Subtype.ext
    rw [Array.set_val_eq]
    apply List.ext_getElem (by grind) fun i hi1 hi2 => ?_
    simp only [List.getElem_set]
    expose_names
    split
    · -- i = N-1: use f_loop_inv at j = r_3 (= N-1) and g_loop_inv to relate r_1[N-1] and arr[N-1].
      apply h_8 r_3 <;>
        (first | grind | (intros; apply h_6 r_3 <;> grind))
    · -- i ≠ N-1: use g_loop_inv at j = i and f_loop_inv to relate.
      apply h_6 (Usize.ofNatCore i (by grind)) <;>
        (first | grind | (intros; apply h_8 (Usize.ofNatCore i (by grind)) <;> grind))
  · -- [f] loop step in N%2=0 branch (j < i'): f_loop_inv branch 1.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply h_16 j <;> grind
  · -- [f] loop step in N%2=0 branch (¬j < i' ∧ j < N): f_loop_inv branch 2.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply h_17 j <;> grind
  · -- N%2=0 post: direct element-wise equality.
    simp at *
    apply Subtype.ext
    apply List.ext_getElem (by grind) fun i hi1 hi2 => ?_
    expose_names
    apply h_4 (Usize.ofNatCore i (by grind)) <;>
      (first | grind | (intros; apply h_6 (Usize.ofNatCore i (by grind)) <;> grind))

end loop_equivalence
