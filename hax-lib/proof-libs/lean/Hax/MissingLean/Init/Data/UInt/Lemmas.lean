attribute [grind] UInt64.lt_ofNat_iff
attribute [grind] UInt64.not_le
attribute [grind] UInt64.toNat_toBitVec
attribute [grind =] UInt64.toNat_toBitVec
attribute [grind] UInt64.toBitVec_ofNat
attribute [grind] UInt64.toNat_add
attribute [grind] UInt64.le_iff_toNat_le
attribute [grind] UInt64.le_ofNat_iff Nat.min_eq_left
attribute [grind =] UInt64.lt_iff_toNat_lt
attribute [grind] UInt64.toNat_ofNat_of_lt
attribute [grind] UInt64.toNat_ofNat_of_lt'

attribute [grind =_] UInt8.le_ofNat_iff
attribute [grind =_] UInt16.le_ofNat_iff
attribute [grind =_] UInt32.le_ofNat_iff
attribute [grind =_] UInt64.le_ofNat_iff

@[grind]
theorem UInt64.umulOverflow_iff (x y : UInt64) :
    BitVec.umulOverflow x.toBitVec y.toBitVec ↔ x.toNat * y.toNat ≥ 2 ^ 64 :=
  by simp [BitVec.umulOverflow]

@[grind]
theorem UInt64.uaddOverflow_iff (x y : UInt64) :
    BitVec.uaddOverflow x.toBitVec y.toBitVec ↔ x.toNat + y.toNat ≥ 2 ^ 64 :=
  by simp [BitVec.uaddOverflow]

@[grind =]
theorem UInt64.toNat_mul_of_lt {a b : UInt64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]

@[grind =]
theorem UInt64.toNat_add_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

@[grind ←]
theorem UInt64.le_self_add {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    a ≤ a + b := by
  rw [le_iff_toNat_le, UInt64.toNat_add_of_lt h]
  exact Nat.le_add_right a.toNat b.toNat

theorem UInt64.succ_le_of_lt {a b : UInt64} (h : a < b) :
    a + 1 ≤ b := by grind

theorem UInt64.add_le_of_le {a b c : UInt64} (habc : a + b ≤ c) (hab : a.toNat + b.toNat < 2 ^ 64):
    a ≤ c := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add_of_lt hab] at *
  omega
