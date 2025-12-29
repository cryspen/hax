
open Lean in
set_option hygiene false in
macro "additional_int_decls" typeName:ident width:term : command => do `(
  namespace $typeName

  def addOverflow (a b : $typeName) : Bool :=
    BitVec.saddOverflow a.toBitVec b.toBitVec

  def subOverflow (a b : $typeName) : Bool :=
    BitVec.ssubOverflow a.toBitVec b.toBitVec

  def mulOverflow (a b : $typeName) : Bool :=
    BitVec.smulOverflow a.toBitVec b.toBitVec

  @[grind]
  theorem addOverflow_iff {a b : $typeName} : addOverflow a b ↔
      a.toInt + b.toInt ≥ 2 ^ ($width - 1) ∨ a.toInt + b.toInt < - 2 ^ ($width - 1) := by
    simp [addOverflow, BitVec.saddOverflow]

  @[grind]
  theorem subOverflow_iff {a b : $typeName} : subOverflow a b ↔
      a.toInt - b.toInt ≥ 2 ^ ($width - 1) ∨ a.toInt - b.toInt < - 2 ^ ($width - 1) := by
    simp [subOverflow, BitVec.ssubOverflow]

  @[grind]
  theorem mulOverflow_iff {a b : $typeName} : mulOverflow a b ↔
      a.toInt * b.toInt ≥ 2 ^ ($width - 1) ∨ a.toInt * b.toInt < - 2 ^ ($width - 1) := by
    simp [mulOverflow, BitVec.smulOverflow]

  @[grind =]
  theorem toInt_add_of_not_addOverflow {x y : $typeName} (h : ¬ addOverflow x y) :
      (x + y).toInt = x.toInt + y.toInt := BitVec.toInt_add_of_not_saddOverflow h

  @[grind =]
  theorem toInt_sub_of_not_subOverflow {x y : $typeName} (h : ¬ subOverflow x y) :
      (x - y).toInt = x.toInt - y.toInt := BitVec.toInt_sub_of_not_ssubOverflow h

  @[grind =]
  theorem toInt_mul_of_not_mulOverflow {x y : $typeName} (h : ¬ mulOverflow x y) :
      (x * y).toInt = x.toInt * y.toInt := BitVec.toInt_mul_of_not_smulOverflow h

  end $typeName
)

additional_int_decls Int8 8
additional_int_decls Int16 16
additional_int_decls Int32 32
additional_int_decls Int64 64
additional_int_decls ISize System.Platform.numBits
