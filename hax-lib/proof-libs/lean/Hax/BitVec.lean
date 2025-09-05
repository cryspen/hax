

namespace BitVec

variable {w: Nat}
variable {x y : (BitVec w)}
variable (h_w: w > 0)

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
theorem toNat_mul_iff_not_umulOverflow :
    ((x * y).toNat = x.toNat * y.toNat ↔ (¬ umulOverflow x y)) := by
  constructor <;> try apply toNat_mul_of_not_umulOverflow
  intros h
  simp only [umulOverflow, ge_iff_le, decide_eq_true_eq, Nat.not_le] at *
  simp [toNat_mul, Nat.mod_eq_iff_lt] at *
  assumption




@[simp]
theorem toInt_add_iff_not_saddOverflow :
    ((x + y).toInt = x.toInt + y.toInt ↔ (¬ saddOverflow x y)) := by
  constructor
  . intros h
    simp only [saddOverflow, Bool.not_eq_true, Bool.or_eq_false_iff] at *
    have := toInt_le (x := (x+y))
    have := le_toInt (x := (x+y))
    constructor <;> simp <;> rw [← h] <;> omega
  . apply toInt_add_of_not_saddOverflow

@[simp]
theorem toInt_sub_iff_not_ssubOverflow :
    ((x - y).toInt = x.toInt - y.toInt ↔ (¬ ssubOverflow x y)) := by
  constructor
  . intros h
    simp only [ssubOverflow, Bool.not_eq_true, Bool.or_eq_false_iff] at *
    have := toInt_le (x := (x-y))
    have := le_toInt (x := (x-y))
    constructor <;> simp <;> rw [← h] <;> omega
  . apply toInt_sub_of_not_ssubOverflow

@[simp]
theorem toInt_mul_iff_not_smulOverflow :
    ((x * y).toInt = x.toInt * y.toInt ↔ (¬ smulOverflow x y)) := by
  constructor
  . intros h
    simp only [smulOverflow, Bool.not_eq_true, Bool.or_eq_false_iff] at *
    have := toInt_le (x := (x*y))
    have := le_toInt (x := (x*y))
    constructor <;> simp <;> rw [← h] <;> omega
  . apply toInt_mul_of_not_smulOverflow

end BitVec
