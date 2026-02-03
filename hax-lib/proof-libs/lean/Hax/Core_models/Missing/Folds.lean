import Hax.Core_models.Extracted
open Std.Do

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-

# Folds

Hax represents for-loops as folds over a range

-/
section Fold

open Core_models.Ops.Control_flow

class Rust_primitives.Hax.Folds {int_type: Type} where
  fold_range {α : Type}
    (s e : int_type)
    (inv : α -> int_type -> RustM Bool)
    (init: α)
    (body : α -> int_type -> RustM α)
    : RustM α
  fold_range_return  {α_acc α_ret : Type}
    (s e: int_type)
    (inv : α_acc -> int_type -> RustM Bool)
    (init: α_acc)
    (body : α_acc -> int_type ->
      RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc ))
    : RustM (ControlFlow α_ret α_acc)

instance : Coe Nat Nat where
  coe x := x

@[simp]
instance {α} [Coe α Nat] [Coe Nat α]: @Rust_primitives.Hax.Folds α where
  fold_range s e inv init body := do
    let mut acc := init
    for i in [s:e] do
      acc := (← body acc i)
    return acc

  fold_range_return {α_acc α_ret} s e inv init body := do
    let mut acc := init
    for i in [s:e] do
      match (← body acc i) with
      | .Break (.Break res ) => return (.Break res)
      | .Break (.Continue ⟨ ⟨ ⟩, res⟩) => return (.Continue res)
      | .Continue acc' => acc := acc'
    pure (ControlFlow.Continue acc)

/-
Nat-based specification for hax_folds_fold_range. It requires that the invariant
holds on the initial value, and that for any index `i` between the start and end
values, executing body of the loop on a value that satisfies the invariant
produces a result that also satisfies the invariant.

-/
@[spec]
theorem Rust_primitives.Hax.Folds.fold_range_spec {α}
  (s e : Nat)
  (inv : α -> Nat -> RustM Bool)
  (init: α)
  (body : α -> Nat -> RustM α) :
  s ≤ e →
  inv init s = pure true →
  (∀ (acc:α) (i:Nat),
    s ≤ i →
    i < e →
    inv acc i = pure true →
    ⦃ ⌜ True ⌝ ⦄
    (body acc i)
    ⦃ ⇓ res => ⌜ inv res (i+1) = pure true ⌝ ⦄) →
  ⦃ ⌜ True ⌝ ⦄
  (Rust_primitives.Hax.Folds.fold_range s e inv init body)
  ⦃ ⇓ r => ⌜ inv r e = pure true ⌝ ⦄
:= by
  intro h_inv_s h_le h_body
  mvcgen [Spec.forIn_list, fold_range]
  case inv1 =>
    simp [Coe.coe]
    exact (⇓ (⟨ suff, _, _ ⟩ , acc ) => ⌜ inv acc (s + suff.length) = pure true ⌝ )
  case vc1.step _ x _ h_list _ h =>
    intros
    simp [Coe.coe] at h_list h
    have ⟨k ,⟨ h_k, h_pre, h_suff⟩⟩ := List.range'_eq_append_iff.mp h_list
    let h_suff := Eq.symm h_suff
    let ⟨ h_x ,_ , h_suff⟩ := List.range'_eq_cons_iff.mp h_suff
    mstart ; mspec h_body <;> simp [Coe.coe] at * <;> try grind
  case vc2.pre | vc4.post.except =>
    simp [Coe.coe] at * <;> try assumption
  case vc3.post.success =>
    simp at *
    suffices (s + (e - s)) = e by (rw [← this]; assumption)
    omega

@[spec]
theorem Rust_primitives.Hax.Folds.usize.fold_range_spec {α}
  (s e : usize)
  (inv : α -> usize -> RustM Bool)
  (init: α)
  (body : α -> usize -> RustM α) :
  s.toNat ≤ e.toNat →
  inv init s = pure true →
  (∀ (acc:α) (i:usize),
    s.toNat ≤ i.toNat →
    i.toNat < e.toNat →
    inv acc i = pure true →
    ⦃ ⌜ True ⌝ ⦄
    (body acc i)
    ⦃ ⇓ res => ⌜ inv res (i+1) = pure true ⌝ ⦄) →
  ⦃ ⌜ True ⌝ ⦄
  (Rust_primitives.Hax.Folds.fold_range s e inv init body)
  ⦃ ⇓ r => ⌜ inv r e = pure true ⌝ ⦄
:= by
  intro h_inv_s h_le h_body
  have : s.toNat < USize64.size := by apply USize64.toNat_lt_size
  have : e.toNat < USize64.size := by apply USize64.toNat_lt_size
  mvcgen [Spec.forIn_list, fold_range]
  case inv1 =>
    simp [Coe.coe]
    exact (⇓ (⟨ suff, _, _ ⟩ , acc ) => ⌜ inv acc (s + (USize64.ofNat suff.length)) = pure true ⌝ )
  case vc2.pre | vc4.post.except =>
    simp [Coe.coe, USize64.ofNat] at * <;> try assumption
  case vc3.post.success =>
    simp at *
    suffices (s + USize64.ofNat (USize64.toNat e - USize64.toNat s)) = e by rwa [← this]
    rw [USize64.ofNat_sub, USize64.ofNat_toNat, USize64.ofNat_toNat] <;> try assumption
    rw (occs := [2])[← USize64.sub_add_cancel (b := s) (a := e)]
    rw [USize64.add_comm]
  case vc1.step _ x _ h_list _ h =>
    intros
    simp [Coe.coe] at h_list h
    have ⟨k ,⟨ h_k, h_pre, h_suff⟩⟩ := List.range'_eq_append_iff.mp h_list
    let h_suff := Eq.symm h_suff
    let ⟨ h_x ,_ , h_suff⟩ := List.range'_eq_cons_iff.mp h_suff
    unfold USize64.size at *
    mstart ; mspec h_body <;> simp [Coe.coe] at *
    . rw [← h_x, Nat.mod_eq_of_lt] <;> grind
    . rw [← h_x, Nat.mod_eq_of_lt] <;> grind [Nat.add_sub_cancel']
    . rw [← h_x, USize64.ofNat_add, USize64.ofNat_toNat]
      rwa [h_pre, List.length_range'] at h
    . rw [h_pre, List.length_range', ← h_x, USize64.ofNat_add, USize64.ofNat_toNat, USize64.add_assoc]
      intro; assumption

end Fold
