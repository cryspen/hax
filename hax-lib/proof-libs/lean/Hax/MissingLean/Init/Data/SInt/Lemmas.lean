attribute [grind =_] Int8.ofNat_le_iff_le
attribute [grind =_] Int16.ofNat_le_iff_le
attribute [grind =_] Int32.ofNat_le_iff_le
attribute [grind =_] Int64.ofNat_le_iff_le

attribute [grind =] Int8.ofNat_toNatClampNeg
attribute [grind =] Int16.ofNat_toNatClampNeg
attribute [grind =] Int32.ofNat_toNatClampNeg
attribute [grind =] Int64.ofNat_toNatClampNeg

open Lean in
set_option hygiene false in
macro "additional_int_lemmas" typeName:ident width:term : command => do `(
  namespace $typeName

    theorem toInt_neg_of_ne_intMin {x : $typeName} (hx : x ≠ minValue) :
        (-x).toInt = -(x.toInt) := by
      have : x.toBitVec ≠ BitVec.intMin $width := by
        refine fun h => hx ?_
        rw [← toBitVec_inj, h, BitVec.intMin_eq_neg_two_pow]
        rfl
      simp only [toInt, minValue, toBitVec_neg, BitVec.toInt_neg_of_ne_intMin this] at *

      theorem ofInt_eq_of_toInt_eq {a : Int} {b : $typeName} (h : b.toInt = a) : ofInt a = b := by
        subst_vars; exact (ofInt_toInt b)

  end $typeName
)

additional_int_lemmas Int8 8
additional_int_lemmas Int16 16
additional_int_lemmas Int32 32
additional_int_lemmas Int64 64
additional_int_lemmas ISize System.Platform.numBits
