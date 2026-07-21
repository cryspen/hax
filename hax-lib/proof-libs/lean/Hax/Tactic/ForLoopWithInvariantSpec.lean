import Hax.Tactic.ForLoopWithInvariant

/-! # Spec lemmas for `forLoopWithInvariant`

Generalized (signed and unsigned) spec lemmas for `Hax.forLoopWithInvariant`, moved
into the library from the `loop_equivalence` example so that they build with the rest
of the proof library.

* `loop_range_spec` is generic over the index scalar type: an unsigned version over
  `UScalar` and a signed version over `IScalar ty` (`.val : Int`). It takes the loop
  body and its per-step contract abstractly, so it never mentions the `Step` dictionary.
* `IteratorRange_next_spec` characterises the `Iterator::next` behaviour of the signed
  `Step` dictionary (here for `I32`).
* `forLoopWithInvariant_spec` is the user-facing `@[spec]` lemma; the signed version
  reduces to `loop_range_spec` discharging the per-step obligation via the signed
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

/-! ## Triple helpers (generic, no scalar type mentioned) -/

section triple_helpers

private abbrev ResultPS := PostShape.except Error (PostShape.except PUnit PostShape.pure)

variable {α : Type}

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

end triple_helpers

/-! ## Loop-over-range spec (signed)

Specialized to `loop` over `core.ops.range.Range (IScalar ty)` (the Aeneas encoding
of a Rust `for i in s..e` loop over a signed integer type). The proof inducts on the
number of remaining steps `(e.val - start.val).toNat` and is, modulo `.val : Int`
instead of `.val : Nat`, identical to the unsigned version. -/

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

/-! ## Iterator `next` spec (signed, `I32`)

Characterises `Iterator::next` for the signed `I32` `Step` dictionary: for `i e : I32`
with `i.val < e.val`, `next` yields `some i` and advances `start` to a value with
`.val = i.val + 1`; when `i.val ≥ e.val` it yields `none`. Unlike the unsigned case
(which uses `overflowing_add`), the signed `forward_checked` casts `1` through a fallible
`usize → u32` `try_from`, `hcast`s it into `I32`, and uses `wrapping_add` guarded by a
`wrapped ≥ start` check; the bound `i.val < e.val ≤ I32.max` rules out the wrap. -/

section next_spec_helpers

/-- `try_from` upper check: `(u32::MAX : usize) = 4294967295`. `u32::MAX` unfolds to
`UScalar.ofNat U32.rMax _`; unfolding the reducible `U32.rMax = 4294967295` exposes a
literal that `scalar_tac` closes (the sibling `min` lemma works the same way, with the
literal `0`). -/
private theorem cast_usize_u32max_val :
    (UScalar.cast UScalarTy.Usize core.num.U32.MAX).val = 4294967295 := by
  simp only [core.num.U32.MAX, U32.rMax]; scalar_tac

/-- `try_from` lower check: `(u32::MIN : usize) = 0`. -/
private theorem cast_usize_u32min_val :
    (UScalar.cast UScalarTy.Usize core.num.U32.MIN).val = 0 := by
  simp only [core.num.U32.MIN]; scalar_tac

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
  simp only [Int.bmod]; split <;> omega

/-- No signed wrap: for `z` within the `i32` range, `bmod` over `2^32` is the identity.
This is what makes `wrapping_add i 1` equal to `i + 1` when `i < i32::MAX`. -/
private theorem bmod_add_one (z : Int) (h1 : -2147483648 ≤ z) (h2 : z ≤ 2147483647) :
    Int.bmod z 4294967296 = z := by
  simp only [Int.bmod]; split <;> omega

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
         simp only [cast_usize_u32max_val, cast_usize_u32min_val, hcast_cast_one_val] at *
         first
           | omega
           | (rw [bmod_add_one (i.val + 1) (by scalar_tac) (by scalar_tac)] at *
              omega))
  · have h_ge' := h_ge (by omega)
    simp_all [compare, compareOfLessAndEq,
      core.I32.Insts.CoreCmpPartialOrdI32, core.mkIPartialOrd]
    mvcgen
    all_goals first
      | exact h_ge'
      | (exfalso
         have hlt : ¬ (i.val < e.val) := by omega
         by_cases hie : i.val = e.val <;> simp_all)

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
    Hax.forLoopWithInvariant inv body { start := s, «end» := e } init
    ⦃ ⇓ r => ⌜ (inv e r).holds ⌝ ⦄ := by
  unfold Hax.forLoopWithInvariant
  apply loop_range_spec _ init s e inv h_le h_init
  intro acc i hsi hie hinv
  simp only [core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next, instStepI32]
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

/-! ## End-to-end signed test

A concrete `for i in (0 : i32) .. 5` loop with the invariant `acc.val = 0`, proven
purely through the signed `forLoopWithInvariant_spec` (which itself routes through
`loop_range_spec` and the signed `IteratorRange_next_spec`). No extraction is involved:
`leancho` alone validates the signed end-to-end path. -/

example :
    ⦃ ⌜ True ⌝ ⦄
    Hax.forLoopWithInvariant
      (fun (_ : I32) (acc : I32) => (ok (acc.val = 0) : Result Prop))
      (fun (_ : I32) (acc : I32) => (ok acc : Result I32))
      { start := (0#i32), «end» := (5#i32) } (0#i32)
    ⦃ ⇓ r => ⌜ (ok (r.val = 0) : Result Prop).holds ⌝ ⦄ := by
  refine forLoopWithInvariant_spec
    (fun _ acc => ok acc) (0#i32) (0#i32) (5#i32)
    (fun _ acc => ok (acc.val = 0)) (by scalar_tac) ?_ ?_
  · -- h_init : `(inv 0 0).holds`, i.e. `(0 : I32).val = 0`
    simp [Result.holds, Triple, WP.wp, PredTrans.apply]
  · -- h_step : the identity body preserves `acc.val = 0`
    intro acc i _ _ hinv
    have hacc : acc.val = 0 := by
      simpa [Result.holds, Triple, WP.wp, PredTrans.apply] using hinv
    simp [Triple, WP.wp, PredTrans.apply, Result.holds, hacc]

end Hax
