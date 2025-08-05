

namespace BitVec

@[simp]
theorem toNat_mul_iff_not_umulOverflow {w} {x y : BitVec w} :
    w > 0 →
    ((x * y).toNat = x.toNat * y.toNat ↔ (¬ umulOverflow x y)) := by
  intros h_w
  constructor <;> try apply toNat_mul_of_not_umulOverflow
  intros h
  simp only [umulOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at *
  simp [toNat_mul, Nat.mod_eq_iff_lt] at *
  assumption


@[simp]
theorem toNat_add_iff_not_uaddOverflow {w} {x y : BitVec w} :
    w > 0 →
    ((x + y).toNat = x.toNat + y.toNat ↔ (¬ uaddOverflow x y)) := by
  intros h_w
  constructor
  . intros h
    simp only [uaddOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at *
    simp [toNat_add, Nat.mod_eq_iff_lt] at *
    assumption
  . apply toNat_add_of_not_uaddOverflow


end BitVec
