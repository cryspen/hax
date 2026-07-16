import Hax.MissingLean.Init.GrindInstances.ToInt

open Lean Grind

@[expose, instance_reducible]
def Int128.natCast : NatCast Int128 where
  natCast x := Int128.ofNat x

@[expose, instance_reducible]
def Int128.intCast : IntCast Int128 where
  intCast x := Int128.ofInt x

attribute [local instance] Int128.intCast in
theorem Int128.intCast_neg (i : Int) : ((-i : Int) : Int128) = -(i : Int128) :=
  Int128.ofInt_neg _

attribute [local instance] Int128.intCast in
theorem Int128.intCast_ofNat (x : Nat) : (OfNat.ofNat (α := Int) x : Int128) = OfNat.ofNat x := Int128.ofInt_eq_ofNat

attribute [local instance] Int128.natCast Int128.intCast in
instance : CommRing Int128 where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := Int128.add_assoc
  add_comm := Int128.add_comm
  add_zero := Int128.add_zero
  neg_add_cancel := Int128.add_left_neg
  mul_assoc := Int128.mul_assoc
  mul_comm := Int128.mul_comm
  mul_one := Int128.mul_one
  one_mul := Int128.one_mul
  left_distrib _ _ _ := Int128.mul_add
  right_distrib _ _ _ := Int128.add_mul
  zero_mul _ := Int128.zero_mul
  mul_zero _ := Int128.mul_zero
  sub_eq_add_neg := Int128.sub_eq_add_neg
  pow_zero := Int128.pow_zero
  pow_succ := Int128.pow_succ
  ofNat_succ x := Int128.ofNat_add x 1
  intCast_neg := Int128.ofInt_neg
  neg_zsmul i x := by
    change (-i : Int) * x = - (i * x)
    simp [Int128.intCast_neg, Int128.neg_mul]
  zsmul_natCast_eq_nsmul n a := congrArg (· * a) (Int128.intCast_ofNat _)

instance : IsCharP Int128 (2 ^ 128) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = Int128.ofInt x := rfl
    rw [this]
    simp [Int128.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add Int128 (.sint 128) := inferInstance
example : ToInt.Neg Int128 (.sint 128) := inferInstance
example : ToInt.Sub Int128 (.sint 128) := inferInstance

instance : ToInt.Pow Int128 (.sint 128) := ToInt.pow_of_semiring (by simp)
