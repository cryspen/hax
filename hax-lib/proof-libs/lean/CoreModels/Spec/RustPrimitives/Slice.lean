import CoreModels.Core.Funs

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP Result

set_option mvcgen.warning false

@[spec]
theorem rust_primitives.slice.array_from_fn_go_spec
    {T F : Type}
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F) (n : Nat)
    (hpure : ∀ k, k < n → ∀ c', c' = c →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn_go inst c n
    ⦃ ⇓ (rl, rc) => ⌜ rc = c ∧ ∃ h : rl.length = n, ∀ i, (hi : i < n) →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ i⟩
                          ⦃ ⇓ r' => ⌜ rl[i] = r'.1 ⌝ ⦄ ⌝ ⦄ := by
  induction n generalizing c with
  | zero =>
    mvcgen [rust_primitives.slice.array_from_fn_go]
    refine ⟨trivial, rfl, ?_⟩
    intro i hi; exact absurd hi (by simp)
  | succ n ih =>
    -- Enrich `hpure` mvcgen's VC still contains the fact that the value came from `call_mut`:
    have hpure' := fun k hk c' hc' => triple_with_self (hpure k hk c' hc')
    mvcgen [rust_primitives.slice.array_from_fn_go, ih, hpure']
    case vc6 =>
      rename_i r_rec h_rec r_call h_call
      obtain ⟨h_receq, h_reclen, h_recpost⟩ := h_rec
      obtain ⟨h_call2, h_callself⟩ := h_call
      refine ⟨h_call2, by simp [h_reclen], ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · -- `i < n`: the `i`-th element comes from the recursion.
        mvcgen [h_recpost]
        grind
      · -- `i = n`: the last element is `r_call.1`, pinned by `h_callself`.
        subst heq
        rw [← h_receq]
        mvcgen [h_callself]
        grind
    all_goals grind

/-- This spec assumes that the closure is not mutated. If the closure was mutated,
we would need a more complex spec that would require the user to provide an invariant. -/
@[spec]
theorem rust_primitives.slice.array_from_fn_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : core.ops.function.FnMut F Std.Usize T) (c : F)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    rust_primitives.slice.array_from_fn N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, (hi : i < N.val) →
                ⦃ ⌜ True ⌝ ⦄ inst.call_mut c ⟨BitVec.ofNat _ i⟩
                          ⦃ ⇓ r => ⌜ r.1 = a.val[i]'(by have := a.property; omega) ⌝ ⦄ ⌝ ⦄ := by
  -- We enrich `hpure` by universally quantifying over the `call_mut` argument instead of fixing
  -- it to `c`:
  have hpure' : ∀ k, k < N.val → ∀ c', c' = c →
      ⦃ ⌜ True ⌝ ⦄ inst.call_mut c' ⟨BitVec.ofNat _ k⟩ ⦃ ⇓ r => ⌜ r.2 = c ⌝ ⦄ :=
    fun k hk c' hc' => hc' ▸ hpure k hk
  mvcgen [rust_primitives.slice.array_from_fn, hpure']
  · -- then-branch
    rename_i r hlen hconj
    obtain ⟨_, _, hpost⟩ := hconj
    intro i hi
    have hp := hpost i hi
    mvcgen [hp]
    grind
  · -- else-branch is impossible: the worker's length equals `N`.
    grind

end CoreModels
