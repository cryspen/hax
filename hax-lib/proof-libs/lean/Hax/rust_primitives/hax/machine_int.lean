
import Hax.rust_primitives.RustM
import Hax.rust_primitives.USize64

open Std.Do
set_option mvcgen.warning false

/- Until notations are introduced by the Lean backend, explicit hax-names
  are also provided -/
namespace rust_primitives.hax.machine_int

@[simp, specset bv, hax_bv_decide]
def eq {α} (x y: α) [BEq α] : RustM Bool := pure (x == y)

@[simp, specset bv, hax_bv_decide]
def ne {α} (x y: α) [BEq α] : RustM Bool := pure (x != y)

@[simp, specset bv, hax_bv_decide]
def lt {α} (x y: α) [LT α] [Decidable (x < y)] : RustM Bool := pure (x < y)

@[simp, specset bv, hax_bv_decide]
def le {α} (x y: α) [LE α] [Decidable (x ≤ y)] : RustM Bool := pure (x ≤ y)

@[simp, specset bv, hax_bv_decide]
def gt {α} (x y: α) [LT α] [Decidable (x > y)] : RustM Bool := pure (x > y)

@[simp, specset bv, hax_bv_decide]
def ge {α} (x y: α) [LE α] [Decidable (x ≥ y)] : RustM Bool := pure (x ≥ y)

attribute [specset bv] bne

@[spec] def bitand {α} (x y: α) [AndOp α] : RustM α := pure (x &&& y)
@[spec] def bitor  {α} (x y: α) [OrOp α]  : RustM α := pure (x ||| y)
@[spec] def bitxor {α} (x y: α) [XorOp α] : RustM α := pure (x ^^^ y)

open Lean in
set_option hygiene false in
macro "declare_comparison_specs" s:(&"signed" <|> &"unsigned") typeName:ident width:term : command => do

  let signed ← match s.raw[0].getKind with
  | `signed => pure true
  | `unsigned => pure false
  | _ => throw .unsupportedSyntax

  if signed then
    return ← `(
      namespace $typeName

      @[specset int]
      def eq_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ eq x y ⦃ ⇓ r => ⌜ r = (x.toInt == y.toInt) ⌝ ⦄ := by
        mvcgen [eq]; rw [← @Bool.coe_iff_coe]; simp [x.toInt_inj]

      @[specset int]
      def ne_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ne x y ⦃ ⇓ r => ⌜ r = (x.toInt != y.toInt) ⌝ ⦄ := by
        mvcgen [ne]; rw [← @Bool.coe_iff_coe]; simp [x.toInt_inj]

      @[specset int]
      def lt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ lt x y ⦃ ⇓ r => ⌜ r = decide (x.toInt < y.toInt) ⌝ ⦄ := by
        mvcgen [lt]; simp [x.lt_iff_toInt_lt]

      @[specset int]
      def le_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ le x y ⦃ ⇓ r => ⌜ r = decide (x.toInt ≤ y.toInt) ⌝ ⦄ := by
        mvcgen [le]; simp [x.le_iff_toInt_le]

      @[specset int]
      def gt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ gt x y ⦃ ⇓ r => ⌜ r = decide (x.toInt > y.toInt ) ⌝ ⦄ := by
        mvcgen [gt]; simp [y.lt_iff_toInt_lt]

      @[specset int]
      def ge_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ge x y ⦃ ⇓ r => ⌜ r = decide (x.toInt ≥ y.toInt) ⌝ ⦄ := by
        mvcgen [ge]; simp [y.le_iff_toInt_le]

      end $typeName
    )
  else return ← `(
      namespace $typeName

      @[specset int]
      def eq_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ eq x y ⦃ ⇓ r => ⌜ r = (x.toNat == y.toNat) ⌝ ⦄ := by
        mvcgen [eq]; rw [← @Bool.coe_iff_coe]; simp [x.toNat_inj]

      @[specset int]
      def ne_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ne x y ⦃ ⇓ r => ⌜ r = (x.toNat != y.toNat) ⌝ ⦄ := by
        mvcgen [ne]; rw [← @Bool.coe_iff_coe]; simp [x.toNat_inj]

      @[specset int]
      def lt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ lt x y ⦃ ⇓ r => ⌜ r = decide (x.toNat < y.toNat) ⌝ ⦄ := by
        mvcgen [lt]

      @[specset int]
      def le_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ le x y ⦃ ⇓ r => ⌜ r = decide (x.toNat ≤ y.toNat) ⌝ ⦄ := by
        mvcgen [le]

      @[specset int]
      def gt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ gt x y ⦃ ⇓ r => ⌜ r = decide (x.toNat > y.toNat ) ⌝ ⦄ := by
        mvcgen [gt]

      @[specset int]
      def ge_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ge x y ⦃ ⇓ r => ⌜ r = decide (x.toNat ≥ y.toNat) ⌝ ⦄ := by
        mvcgen [ge]

      end $typeName
  )

declare_comparison_specs signed Int8 8
declare_comparison_specs signed Int16 16
declare_comparison_specs signed Int32 32
declare_comparison_specs signed Int64 64
declare_comparison_specs signed ISize System.Platform.numBits
declare_comparison_specs unsigned UInt8 8
declare_comparison_specs unsigned UInt16 16
declare_comparison_specs unsigned UInt32 32
declare_comparison_specs unsigned UInt64 64
declare_comparison_specs unsigned USize64 64

end rust_primitives.hax.machine_int
