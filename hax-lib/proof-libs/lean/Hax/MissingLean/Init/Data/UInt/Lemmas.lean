attribute [grind] USize.lt_ofNat_iff
attribute [grind] USize.not_le
attribute [grind] USize.toNat_toBitVec
attribute [grind =] USize.toNat_toBitVec
attribute [grind] USize.toBitVec_ofNat
attribute [grind] USize.toNat_add
attribute [grind] USize.le_iff_toNat_le
attribute [grind] USize.le_ofNat_iff Nat.min_eq_left
attribute [grind =] USize.lt_iff_toNat_lt
attribute [grind] USize.toNat_ofNat_of_lt
attribute [grind] USize.toNat_ofNat_of_lt'
attribute [grind =_] UInt8.le_ofNat_iff
attribute [grind =_] UInt16.le_ofNat_iff
attribute [grind =_] UInt32.le_ofNat_iff
attribute [grind =_] UInt64.le_ofNat_iff

@[grind =]
theorem UInt64.toNat_add_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

theorem UInt64.succ_le_of_lt {a b : UInt64} (h : a < b) :
    a + 1 ≤ b := by grind

theorem UInt64.add_le_of_le {a b c : UInt64} (habc : a + b ≤ c) (hab : a.toNat + b.toNat < 2 ^ 64):
    a ≤ c := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_add_of_lt hab] at *
  omega

@[grind]
theorem USize.umulOverflow_iff (x y : USize) :
    BitVec.umulOverflow x.toBitVec y.toBitVec ↔ x.toNat * y.toNat ≥ 2 ^ System.Platform.numBits :=
  by simp [BitVec.umulOverflow]

@[grind]
theorem USize.uaddOverflow_iff (x y : USize) :
    BitVec.uaddOverflow x.toBitVec y.toBitVec ↔ x.toNat + y.toNat ≥ 2 ^ System.Platform.numBits :=
  by simp [BitVec.uaddOverflow]

@[grind =]
theorem USize.toNat_mul_of_lt {a b : USize} (h : a.toNat * b.toNat < 2 ^ System.Platform.numBits) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [USize.toNat_mul, Nat.mod_eq_of_lt h]

@[grind =]
theorem USize.toNat_add_of_lt {a b : USize} (h : a.toNat + b.toNat < 2 ^ System.Platform.numBits) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt h]

@[grind ←]
theorem USize.le_self_add {a b : USize} (h : a.toNat + b.toNat < 2 ^ System.Platform.numBits) :
    a ≤ a + b := by
  grind
