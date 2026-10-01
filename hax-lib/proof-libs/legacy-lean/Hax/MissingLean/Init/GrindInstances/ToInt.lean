import Hax.MissingLean.Init.Data.SInt.Lemmas_Int128
import Hax.MissingLean.Init.Data.UInt.Lemmas_UInt128

open Lean.Grind

instance : ToInt UInt128 (.uint 128) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := private UInt128.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (UInt128.toNat_lt x)

@[simp] theorem toInt_uint128 (x : UInt128) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero UInt128 (.uint 128) where
  toInt_zero := by simp

instance : ToInt.OfNat UInt128 (.uint 128) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add UInt128 (.uint 128) where
  toInt_add x y := by simp

instance : ToInt.Mul UInt128 (.uint 128) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod UInt128 (.uint 128) where
  toInt_mod x y := by simp

instance : ToInt.Div UInt128 (.uint 128) where
  toInt_div x y := by simp

instance : ToInt.LE UInt128 (.uint 128) where
  le_iff x y := by simpa using UInt128.le_iff_toBitVec_le

instance : ToInt.LT UInt128 (.uint 128) where
  lt_iff x y := by simpa using UInt128.lt_iff_toBitVec_lt


instance : ToInt Int128 (.sint 128) where
  toInt x := x.toInt
  toInt_inj x y w := private Int128.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨Int128.le_toInt x, Int128.toInt_lt x⟩

@[simp] theorem toInt_int128 (x : Int128) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero Int128 (.sint 128) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int128).toInt = _
    rw [Int128.toInt_zero]

instance : ToInt.OfNat Int128 (.sint 128) where
  toInt_ofNat x := by
    rw [toInt_int128, Int128.toInt_ofNat, Int128.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add Int128 (.sint 128) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul Int128 (.sint 128) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.SInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.LE Int128 (.sint 128) where
  le_iff x y := by simpa using Int128.le_iff_toInt_le

instance : ToInt.LT Int128 (.sint 128) where
  lt_iff x y := by simpa using Int128.lt_iff_toInt_lt
