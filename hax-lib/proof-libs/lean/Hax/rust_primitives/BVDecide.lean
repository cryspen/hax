import Hax.rust_primitives.RustM

open Std.Do

/-

# BV_Decide Lemmas

In the following, we define an encoding of the entire `RustM` monad so that we can run `bv_decide`
on equalities between `RustM` values.

-/

/-- We encode `RustM` values into the following structure to be able to run `bv_decide`: -/
structure BVRustM (α : Type) where
  ok : Bool
  val : α
  err : BitVec 3

/-- Encodes `RustM` values into `BVRustM` to be able to run `bv_decide`. -/
def RustM.toBVRustM {α} [Inhabited α] : RustM α → BVRustM α
| ok v                      => ⟨ true, v, 0 ⟩
| fail .assertionFailure    => ⟨ false, default, 0 ⟩
| fail .integerOverflow     => ⟨ false, default, 1 ⟩
| fail .divisionByZero      => ⟨ false, default, 2 ⟩
| fail .arrayOutOfBounds    => ⟨ false, default, 3 ⟩
| fail .maximumSizeExceeded => ⟨ false, default, 4 ⟩
| fail .panic               => ⟨ false, default, 5 ⟩
| fail .undef               => ⟨ false, default, 6 ⟩
| div                       => ⟨ false, default, 7 ⟩

attribute [hax_bv_decide] Coe.coe bind pure

@[hax_bv_decide] theorem RustM.toBVRustM_ok {α} [Inhabited α] {v : α} :
    (RustM.ok v).toBVRustM = ⟨ true, v, 0 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_assertionFailure {α} [Inhabited α] :
    (RustM.fail .assertionFailure : RustM α).toBVRustM = ⟨ false, default, 0 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_integerOverflow {α} [Inhabited α] :
    (RustM.fail .integerOverflow : RustM α).toBVRustM = ⟨ false, default, 1 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_divisionByZero {α} [Inhabited α] :
    (RustM.fail .divisionByZero : RustM α).toBVRustM = ⟨ false, default, 2 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_arrayOutOfBounds {α} [Inhabited α] :
    (RustM.fail .arrayOutOfBounds : RustM α).toBVRustM = ⟨ false, default, 3 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_maximumSizeExceeded {α} [Inhabited α] :
    (RustM.fail .maximumSizeExceeded: RustM α).toBVRustM = ⟨ false, default, 4 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_panic {α} [Inhabited α] :
    (RustM.fail .panic : RustM α).toBVRustM = ⟨ false, default, 5 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_undef {α} [Inhabited α] :
    (RustM.fail .undef : RustM α).toBVRustM = ⟨ false, default, 6 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_div {α} [Inhabited α] :
    (RustM.div : RustM α ).toBVRustM = ⟨ false, default, 7 ⟩ := rfl

@[hax_bv_decide]
theorem RustM.toBVRustM_ite {α} [Inhabited α] {c : Prop} [Decidable c]  (x y : RustM α) :
    (if c then x else y).toBVRustM = (if c then x.toBVRustM else y.toBVRustM) := by grind

@[hax_bv_decide]
theorem RustM.beq_iff_toBVRustM_eq {α} [Inhabited α] [DecidableEq α] (x y : RustM α) :
    decide (x = y) =
      (x.toBVRustM.ok == y.toBVRustM.ok &&
       x.toBVRustM.val == y.toBVRustM.val &&
       x.toBVRustM.err == y.toBVRustM.err) := by
  by_cases h : x = y
  · simp [h]
  · revert h
    cases x using RustM.toBVRustM.match_1 <;>
    cases y using RustM.toBVRustM.match_1 <;>
    grind [toBVRustM]

@[hax_bv_decide]
theorem RustM.toBVRustM_bind {α β} [Inhabited α] [Inhabited β] (x : RustM α) (f : α → RustM β) :
  (x.bind f).toBVRustM =
    if x.toBVRustM.ok
    then (f x.toBVRustM.val).toBVRustM
    else {x.toBVRustM with val := default} := by
  apply RustM.toBVRustM.match_1.splitter _ x <;> simp [bind, toBVRustM]

@[hax_bv_decide]
theorem RustM.Triple_iff_BitVec {α} [Inhabited α]
    (a : Prop) [Decidable a] (b : α → Prop) (x : RustM α) [Decidable (b x.toBVRustM.val)] :
    ⦃ ⌜ a ⌝ ⦄ x ⦃ ⇓ r => ⌜ b r ⌝ ⦄ ↔
      (!decide a || (x.toBVRustM.ok && decide (b x.toBVRustM.val))) := by
  cases x using RustM.toBVRustM.match_1 <;>
    by_cases a
      <;> simp only [Triple, PredTrans.apply, wp, SPred.entails_nil, SPred.down_pure,
        Decidable.imp_iff_not_or, toBVRustM, BitVec.ofNat_eq_ofNat, Bool.false_and, Bool.or_false,
        Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, or_iff_left_iff_imp,
        Bool.true_and, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, decide_eq_true_eq]
      <;> try rfl
  all_goals exact fun x => False.elim x

/-- This lemma is used to make some variants of `>>>?` accessible for `bv_decide` -/
@[hax_bv_decide]
theorem Int32.to_Int64_toNatClampNeg : (Int32.toNatClampNeg 1).toInt64 = 1 := rfl
