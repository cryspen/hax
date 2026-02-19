import Hax.MissingLean.Init.GrindInstances.ToInt

open Lean Grind

namespace UInt128

/-- Variant of `UInt128.ofNat_mod_size` replacing `2 ^ 128` with `18446744073709551616`.-/
theorem ofNat_mod_size' : ofNat (x % 18446744073709551616) = ofNat x := ofNat_mod_size

@[expose, instance_reducible]
def natCast : NatCast UInt128 where
  natCast x := UInt128.ofNat x

@[expose, instance_reducible]
def intCast : IntCast UInt128 where
  intCast x := UInt128.ofInt x

attribute [local instance] natCast intCast

theorem intCast_neg (x : Int) : ((-x : Int) : UInt128) = - (x : UInt128) := by
  simp only [Int.cast, IntCast.intCast, UInt128.ofInt_neg]

theorem intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : UInt128) = OfNat.ofNat x := by
    -- A better proof would be welcome!
    simp only [Int.cast, IntCast.intCast]
    rw [UInt128.ofInt]
    rw [Int.toNat_emod (Int.zero_le_ofNat x) (by decide)]
    erw [Int.toNat_natCast]
    rw [Int.toNat_pow_of_nonneg (by decide)]
    simp +instances only [ofNat, BitVec.ofNat, Fin.Internal.ofNat_eq_ofNat, Fin.ofNat, Int.reduceToNat, Nat.dvd_refl,
      Nat.mod_mod_of_dvd, instOfNat]
    try rfl

end UInt128


attribute [local instance] UInt128.natCast UInt128.intCast in
instance : CommRing UInt128 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := UInt128.add_assoc
  add_comm := UInt128.add_comm
  add_zero := UInt128.add_zero
  neg_add_cancel := UInt128.add_left_neg
  mul_assoc := UInt128.mul_assoc
  mul_comm := UInt128.mul_comm
  mul_one := UInt128.mul_one
  one_mul := UInt128.one_mul
  left_distrib _ _ _ := UInt128.mul_add
  right_distrib _ _ _ := UInt128.add_mul
  zero_mul _ := UInt128.zero_mul
  mul_zero _ := UInt128.mul_zero
  sub_eq_add_neg := UInt128.sub_eq_add_neg
  pow_zero := UInt128.pow_zero
  pow_succ := UInt128.pow_succ
  ofNat_succ x := UInt128.ofNat_add x 1
  intCast_neg := UInt128.ofInt_neg
  intCast_ofNat := UInt128.intCast_ofNat
  neg_zsmul i a := by
    change (-i : Int) * a = - (i * a)
    simp [UInt128.intCast_neg, UInt128.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (UInt128.intCast_ofNat _)

instance : IsCharP UInt128 18446744073709551616 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = UInt128.ofNat x := rfl
    simp [this, UInt128.ofNat_eq_iff_mod_eq_toNat])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add UInt128 (.uint 128) := inferInstance
example : ToInt.Neg UInt128 (.uint 128) := inferInstance
example : ToInt.Sub UInt128 (.uint 128) := inferInstance

instance : ToInt.Pow UInt128 (.uint 128) := ToInt.pow_of_semiring (by simp)
