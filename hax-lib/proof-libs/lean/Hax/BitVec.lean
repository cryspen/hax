

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


end BitVec
