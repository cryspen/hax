import Hax.Lib

attribute [grind =] USize.lt_iff_toNat_lt

attribute [grind] Array.size_extract

attribute [grind] USize.toBitVec_ofNat
attribute [grind =] BitVec.toNat_ofNat
attribute [grind =] Nat.mod_eq_of_lt
attribute [grind =] USize.toNat_toBitVec
attribute [grind] BitVec.umulOverflow
attribute [grind] BitVec.uaddOverflow
attribute [grind] USize.toNat_toBitVec
attribute [grind] Vector.size_toArray

attribute [grind] USize.lt_ofNat_iff
attribute [grind] USize.not_le

@[grind]
theorem USize.toNat_ofNat_of_lt'' {x : Nat} (h : x < USize.size) :
    ToNat.toNat (OfNat.ofNat x : USize) = x :=
  USize.toNat_ofNat_of_lt h


@[grind]
theorem USize.umulOverflow_iff (x y : USize) :
    BitVec.umulOverflow x.toBitVec y.toBitVec ↔ x.toNat * y.toNat ≥ 2 ^ System.Platform.numBits :=
  by simp [BitVec.umulOverflow]

@[grind]
theorem USize.uaddOverflow_iff (x y : USize) :
    BitVec.uaddOverflow x.toBitVec y.toBitVec ↔ x.toNat + y.toNat ≥ 2 ^ System.Platform.numBits :=
  by simp [BitVec.uaddOverflow]

attribute [grind] USize.toNat_add USize.le_iff_toNat_le

@[grind ←]
theorem USize.le_self_add (a b : USize) (h : a.toNat + b.toNat < 2 ^ System.Platform.numBits) : a ≤ a + b := by
  grind

@[grind]
theorem System.Platform.two_pow_numBits_eq :
  2 ^ System.Platform.numBits = 4294967296 ∨ 2 ^ System.Platform.numBits = 18446744073709551616 := by
  rcases System.Platform.numBits_eq <;> simp [*]

@[grind =]
theorem USize.toNat_mul_of_lt (a b : USize) (h : a.toNat * b.toNat < 2 ^ System.Platform.numBits) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [USize.toNat_mul, Nat.mod_eq_of_lt h]

@[grind =]
theorem USize.toNat_add_of_lt (a b : USize) (h : a.toNat + b.toNat < 2 ^ System.Platform.numBits) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, Nat.mod_eq_of_lt h]

attribute [grind] USize.le_ofNat_iff Nat.min_eq_left
