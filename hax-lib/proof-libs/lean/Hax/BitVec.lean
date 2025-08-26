

namespace BitVec

variable {w: Nat}
variable {x y : (BitVec w)}
variable (h_w: w > 0)

@[simp]
theorem toNat_mul_iff_not_umulOverflow :
    ((x * y).toNat = x.toNat * y.toNat ↔ (¬ umulOverflow x y)) := by
  constructor <;> try apply toNat_mul_of_not_umulOverflow
  intros h
  simp only [umulOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at *
  simp [toNat_mul, Nat.mod_eq_iff_lt] at *
  assumption


@[simp]
theorem toNat_add_iff_not_uaddOverflow :
    ((x + y).toNat = x.toNat + y.toNat ↔ (¬ uaddOverflow x y)) := by
  constructor
  . intros h
    simp only [uaddOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at *
    simp [toNat_add, Nat.mod_eq_iff_lt] at *
    assumption
  . apply toNat_add_of_not_uaddOverflow


@[simp]
theorem toInt_add_iff_not_uaddOverflow :
    ((x + y).toInt = x.toInt + y.toInt ↔ (¬ saddOverflow x y)) := by
  constructor
  . intros h
    simp only [saddOverflow] at *
    rw [not_eq]
    rw [Int.not_le]
    simp [toInt_add, Int.mod_eq_iff_lt] at *
    assumption
  . apply toInt_add_of_not_uaddOverflow


end BitVec
