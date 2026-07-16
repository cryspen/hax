import LoopEquivalence.Extraction.Funs
import LoopEquivalence.Proofs.MissingSpecs
import Hax
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result ControlFlow Error
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option hax_mvcgen.warnings false

namespace loop_equivalence

-- Local automation configuration
attribute [local spec] g f op g_loop g_loop.body f_loop f_loop.body g_loop_inv f_loop_inv g.post
attribute [local spec] core.Array.Insts.CoreCloneClone.clone

set_option maxHeartbeats 1000000
theorem g_spec {N : Usize} (arr : Array U64 N) :
    ⦃ ⌜ True ⌝ ⦄
    g arr
    ⦃ ⇓ future_arr => ⌜(do let x ← f arr; pure (future_arr == x) : Result Bool).holds ⌝ ⦄ := by
  unfold g g_loop g_loop.body f f_loop f_loop.body
  for_loop_with_invariant fun i r =>
    pure (∀ (j : Usize), (do let a ← g_loop_inv r arr i j; pure (a = true)).holds)
  for_loop_with_invariant fun i r =>
    pure (∀ (j : Usize), (do let a ← f_loop_inv r arr i j; pure (a = true)).holds)
  hax_mvcgen
  all_goals try grind
  · -- [g] loop step (j < i'): g_loop_inv branch 1.
    expose_names
    apply (‹∀ (j : Usize) (p : Prop), _ → _ → _ → p›) j <;> grind
  · -- [g] loop step (¬j < i' ∧ j < N): g_loop_inv branch 2.
    expose_names
    apply (‹∀ (j : Usize) (p : Prop), _ → _ → _ → p›) j <;> grind
  · -- [f] loop step in N%2>0 branch (j < i'): f_loop_inv branch 1.
    expose_names
    apply (‹∀ (j : Usize) (p : Prop), _ → _ → _ → p›) j <;> grind
  · -- [f] loop step in N%2>0 branch (¬j < i' ∧ j < N): f_loop_inv branch 2.
    expose_names
    apply (‹∀ (j : Usize) (p : Prop), _ → _ → _ → p›) j <;> grind
  · -- N%2>0 post: g's update at N-1 vs f_loop's full result.
    simp only [beq_iff_eq]; try subst_vars
    apply Subtype.ext
    rw [Array.set_val_eq]
    apply List.ext_getElem (by grind) fun i hi1 hi2 => ?_
    simp only [List.getElem_set]
    expose_names
    split
    · apply h_8 r_3 <;>
        (first | grind | (intros; apply h_7 r_3 <;> simp <;> grind))
    · apply h_7 (Usize.ofNatCore i (by grind)) <;>
        (first | grind | (intros; apply h_8 (Usize.ofNatCore i (by grind))
          <;> simp only [UScalar.ofNatCore_val_eq] at * <;> grind))
  · -- [f] loop step in N%2=0 branch (j < i'): f_loop_inv branch 1.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply (‹∀ (j : Usize) (p : Prop), _ → _ → _ → p›) j <;> grind
  · -- [f] loop step in N%2=0 branch (¬j < i' ∧ j < N): f_loop_inv branch 2.
    try (simp only [UScalar.ofNatCore_val_eq] at *); expose_names
    apply (‹∀ (j : Usize) (p : Prop), _ → _ → _ → p›) j <;> grind
  · -- N%2=0 post: direct element-wise equality.
    simp only [beq_iff_eq]
    apply Subtype.ext
    apply List.ext_getElem (by grind) fun i hi1 hi2 => ?_
    expose_names
    apply h_4 (Usize.ofNatCore i (by grind)) <;>
      (first | grind | (intros; apply h_3 (Usize.ofNatCore i (by grind))
      <;> simp only [UScalar.ofNatCore_val_eq] <;> grind))

end loop_equivalence
