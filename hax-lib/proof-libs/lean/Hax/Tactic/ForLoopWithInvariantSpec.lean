import Hax.Tactic.ForLoopWithInvariant

/-! # Spec lemmas for `forLoopWithInvariant`

Signed (`I32`) and unsigned (`Usize`) spec lemmas for `Hax.forLoopWithInvariant`.

* `IteratorRange_next_spec` / `IteratorRange_next_spec_usize` characterise the
  `Iterator::next` behaviour of the signed / unsigned `Step` dictionary.
* `forLoopWithInvariant_spec` / `forLoopWithInvariant_spec_usize` are the user-facing
  `@[spec]` lemmas; each reduces to the corresponding `loop_range_spec` (in
  `Hax.MissingAeneas`), discharging the per-step obligation via the matching
  `IteratorRange_next_spec`. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option mvcgen.warning false

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
open Std.Tactic

namespace Hax

/-! ## Iterator `next` spec (signed, `I32`)

Characterises `Iterator::next` for the signed `I32` `Step` dictionary: for `i e : I32`
with `i.val < e.val`, `next` yields `some i` and advances `start` to a value with
`.val = i.val + 1`; when `i.val ≥ e.val` it yields `none`. Unlike the unsigned case
(which uses `overflowing_add`), the signed `forward_checked` casts `1` through a fallible
`usize → u32` `try_from`, `hcast`s it into `I32`, and uses `wrapping_add` guarded by a
`wrapped ≥ start` check; the bound `i.val < e.val ≤ I32.max` rules out the wrap. -/

section next_spec_helpers

/-- The step `1 : usize`, cast to `u32` and `hcast` into `i32`, has value `1`. We reduce
`hcast`/`cast` through `BitVec.toInt_setWidth` (rather than kernel-reducing the opaque
`usize` bit-width), rewrite the inner `u32` value to `1` (`simp` proves the narrowing
cast value), and finish the resulting `Int.bmod 1 (2^32) = 1` by case split + `omega`. -/
private theorem hcast_cast_one_val :
    (UScalar.hcast IScalarTy.I32 (UScalar.cast UScalarTy.U32 (1#usize))).val = 1 := by
  have hcv : (UScalar.cast UScalarTy.U32 1#usize).bv.toNat = 1 := by
    have h : (UScalar.cast UScalarTy.U32 1#usize).val = 1 := by simp
    simpa only [UScalar.val] using h
  simp only [UScalar.hcast, BitVec.truncate_eq_setWidth, IScalar.val, BitVec.toInt_setWidth,
    UScalarTy.numBits, IScalarTy.numBits, hcv]
  grind

/-- No signed wrap: for `z` within the `i32` range, `bmod` over `2^32` is the identity.
This is what makes `wrapping_add i 1` equal to `i + 1` when `i < i32::MAX`. -/
private theorem bmod_add_one (z : Int) (h1 : -2147483648 ≤ z) (h2 : z ≤ 2147483647) :
    Int.bmod z 4294967296 = z := by
  grind

/-- The value produced by the `i32` `forward_checked` step: `wrapping_add i 1 = i + 1`
whenever `i` stays below `i32::MAX` (so no wrap occurs). -/
private theorem i32_wrapping_add_one_val (i : I32)
    (h1 : -2147483648 ≤ i.val) (h2 : i.val ≤ 2147483646) :
    (i.wrapping_add (UScalar.hcast IScalarTy.I32 (UScalar.cast UScalarTy.U32 1#usize))).val
      = i.val + 1 := by
  simp only [I32.wrapping_add_val_eq, hcast_cast_one_val, Nat.reducePow]
  exact bmod_add_one _ (by scalar_tac) (by scalar_tac)

end next_spec_helpers

@[spec]
theorem IteratorRange_next_spec (i e : I32) {Q}
    (h_lt : (h : i.val < e.val) →
      ∀ (s : I32), s.val = i.val + 1 →
        (Q.1 (some i, { start := s, «end» := e })).down)
    (h_ge : i.val ≥ e.val →
      (Q.1 (none, { start := i, «end» := e })).down) :
    ⦃ ⌜ True ⌝ ⦄
    core.IteratorRange.next core.I32.Insts.CoreIterRangeStep
      { start := i, «end» := e }
    ⦃ Q ⦄ := by
  unfold core.IteratorRange.next core.I32.Insts.CoreIterRangeStep
  by_cases h : i.val < e.val
  · have h_lt' := h_lt h
    simp_all [compare, compareOfLessAndEq,
      core.I32.Insts.CoreCmpPartialOrdI32, core.mkIPartialOrd,
      core.I32.Insts.CoreCloneClone.clone,
      core.I32.Insts.CoreIterRangeStep.forward_checked,
      core.U32.Insts.CoreConvertTryFromUsizeTryFromIntError.try_from,
      core.num.U32.MAX, core.num.U32.MIN,
      core.num.I32.wrapping_add, rust_primitives.arithmetic.wrapping_add_i32]
    mvcgen
    all_goals first
      | (refine h_lt' _ ?_
         subst_vars
         exact i32_wrapping_add_one_val i (by scalar_tac) (by scalar_tac))
      | (exfalso
         subst_vars
         simp only [U32.rMax, hcast_cast_one_val] at *
         first
           | scalar_tac
           | (rw [bmod_add_one (i.val + 1) (by scalar_tac) (by scalar_tac)] at *
              scalar_tac))
  · have h_ge' := h_ge (by omega)
    simp_all [compare, compareOfLessAndEq,
      core.I32.Insts.CoreCmpPartialOrdI32, core.mkIPartialOrd]
    mvcgen
    all_goals first
      | exact h_ge'
      | (exfalso
         have hlt : ¬ (i.val < e.val) := by omega
         by_cases hie : i.val = e.val <;> simp_all)

/-! ## Iterator `next` spec (unsigned, `Usize`)

Characterises `Iterator::next` for the unsigned `Usize` `Step` dictionary: for `i e : Usize`
with `i.val < e.val`, `next` yields `some i` and advances `start` by one via
`overflowing_add` (no overflow, since `i.val + 1 ≤ Usize.max`); when `i.val ≥ e.val` it
yields `none`. -/

@[spec]
theorem IteratorRange_next_spec_usize (i e : Usize) {Q}
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

/-! ## User-facing `@[spec]` lemma (signed, `I32`)

Reduces to `loop_range_spec`, discharging the per-step obligation with the signed
`IteratorRange_next_spec`: the iterator produces the current index and advances by one
while `i < e`, and short-circuits at `i = e`. -/

@[spec]
theorem forLoopWithInvariant_spec {β : Type}
    (body : I32 → β → Result β)
    (init : β) (s e : I32) (inv : I32 → β → Result Prop)
    (h_le : s.val ≤ e.val)
    (h_init : (inv s init).holds)
    (h_step : ∀ acc (i : I32), s.val ≤ i.val → i.val < e.val →
      (inv i acc).holds →
      ⦃ ⌜ True ⌝ ⦄
      body i acc
      ⦃ ⇓ r => ⌜ ∀ (i' : I32), i'.val = i.val + 1 → (inv i' r).holds ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    Hax.forLoopWithInvariant core.I32.Insts.CoreIterRangeStep inv body
      { start := s, «end» := e } init
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  unfold Hax.forLoopWithInvariant
  apply loop_range_spec _ init s e inv h_le h_init
  intro acc i hsi hie hinv
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next]
  mvcgen [IteratorRange_next_spec]
  case vc1.h_lt =>
    rename_i hlt s' hs'
    have hbody := h_step acc i hsi hlt hinv
    obtain ⟨r, hbeq⟩ := triple_noThrow_exists_ok hbody
    have hh := (triple_noThrow_elim hbody hbeq) s' hs'
    simp [Triple, WP.wp, PredTrans.apply, hbeq, Result.holds] at hh ⊢
    exact ⟨hlt, hs', hh⟩
  case vc2.h_ge =>
    rename_i hge
    have hi_eq_e : i = e := IScalar.eq_imp _ _ (by omega)
    subst hi_eq_e
    simpa [Triple, WP.wp, PredTrans.apply, Result.holds] using hinv

/-! ## User-facing `@[spec]` lemma (unsigned, `Usize`)

Reduces to `loop_range_spec_unsigned`, discharging the per-step obligation for the
unsigned `Step` dictionary: `next` yields `(some i, iter')` with `iter'.start.val = i.val + 1`
while `i < e`, and short-circuits at `i = e`. -/

@[spec]
theorem forLoopWithInvariant_spec_usize {β : Type}
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
    Hax.forLoopWithInvariant core.Usize.Insts.CoreIterRangeStep inv body
      { start := s, «end» := e } init
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  unfold Hax.forLoopWithInvariant
  apply loop_range_spec_unsigned _ init s e inv h_le h_init
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

end Hax
