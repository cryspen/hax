open Lean in
set_option hygiene false in
macro "additional_uint_decls" typeName:ident width:term : command => do
  let mut cmds := ← Syntax.getArgs <$> `(
    namespace $typeName

    theorem toNat_add_of_lt {x y : $typeName} (h : x.toNat + y.toNat < 2 ^ $width) :
        (x + y).toNat = x.toNat + y.toNat := BitVec.toNat_add_of_lt h

    theorem toNat_sub_of_le' {x y : $typeName} (h : y.toNat ≤ x.toNat) :
        (x - y).toNat = x.toNat - y.toNat := BitVec.toNat_sub_of_le h

    theorem toNat_mul_of_lt {x y : $typeName} (h : x.toNat * y.toNat < 2 ^ $width) :
        (x * y).toNat = x.toNat * y.toNat := BitVec.toNat_mul_of_lt h

    def addOverflow (a b : $typeName) : Bool :=
      BitVec.uaddOverflow a.toBitVec b.toBitVec

    def subOverflow (a b : $typeName) : Bool :=
      BitVec.usubOverflow a.toBitVec b.toBitVec

    def mulOverflow (a b : $typeName) : Bool :=
      BitVec.umulOverflow a.toBitVec b.toBitVec

    @[grind .]
    theorem addOverflow_iff {a b : $typeName} : addOverflow a b ↔ a.toNat + b.toNat ≥ 2 ^ $width :=
      decide_eq_true_iff

    @[grind .]
    theorem subOverflow_iff {a b : $typeName} : subOverflow a b ↔ a.toNat < b.toNat :=
      decide_eq_true_iff

    @[grind .]
    theorem mulOverflow_iff {a b : $typeName} : mulOverflow a b ↔ a.toNat * b.toNat ≥ 2 ^ $width :=
      decide_eq_true_iff

    end $typeName
  )
  return ⟨mkNullNode cmds⟩

additional_uint_decls UInt8 8
additional_uint_decls UInt16 16
additional_uint_decls UInt32 32
additional_uint_decls UInt64 64
additional_uint_decls USize System.Platform.numBits
