import Hax.Rust_primitives.USize64
import Hax.Tactic.Init
import Hax.Rust_primitives.RustM

open Std.Do
set_option mvcgen.warning false

/-
  Integer types are represented as the corresponding type in Lean
-/
abbrev u8 := UInt8
abbrev u16 := UInt16
abbrev u32 := UInt32
abbrev u64 := UInt64
abbrev usize := USize64
abbrev u128 := BitVec 128
abbrev i8 := Int8
abbrev i16 := Int16
abbrev i32 := Int32
abbrev i64 := Int64
abbrev i128 := BitVec 128
abbrev isize := ISize

abbrev f32 := Float32
abbrev f64 := Float

/-- Class of objects that can be transformed into Nat -/
class ToNat (α: Type) where
  toNat : α -> Nat

attribute [grind] ToNat.toNat

@[simp, grind]
instance : ToNat usize where
  toNat x := x.toNat
@[simp, grind]
instance : ToNat u64 where
  toNat x := x.toNat
@[simp, grind]
instance : ToNat u32 where
  toNat x := x.toNat
@[simp, grind]
instance : ToNat u16 where
  toNat x := x.toNat
@[simp, grind]
instance : ToNat Nat where
  toNat x := x

/-
  Coercions between integer types
-/
-- TODO : make sure all are necessary, document their use-cases
@[simp, spec]
instance : Coe i32 (RustM i64) where
  coe x := pure (x.toInt64)

@[simp]
instance : Coe usize Nat where
  coe x := x.toNat

@[simp]
instance : Coe Nat u32 where
  coe n := UInt32.ofNat n

@[simp]
instance : Coe u32 Nat where
  coe x := x.toNat

@[simp]
instance : Coe Nat usize where
  coe x := USize64.ofNat x

@[simp]
instance : Coe usize u32 where
  coe x := x.toUInt32

@[simp]
instance : Coe usize (RustM u32) where
  coe x := if x.toNat < UInt32.size then pure (x.toUInt32)
           else RustM.fail .integerOverflow

@[simp]
instance {n: Nat} : OfNat (RustM Nat) n where
  ofNat := pure (n)

instance {α n} [i: OfNat α n] : OfNat (RustM α) n where
  ofNat := pure (i.ofNat)

abbrev Hax_lib.Int.Int : Type := _root_.Int
abbrev Rust_primitives.Hax.Int.from_machine {α} [ToNat α] (x : α) : RustM Int := Int.ofNat (ToNat.toNat x)

infixl:58 " ^^^? " => fun a b => pure (HXor.hXor a b)
infixl:60 " &&&? " => fun a b => pure (HAnd.hAnd a b)

/- Until notations are not introduced by the Lean backend, explicit hax-names
  are also provided -/
namespace Rust_primitives.Hax.Machine_int

@[simp, hax_bv_decide]
def eq {α} (x y: α) [BEq α] : RustM Bool := pure (x == y)

@[simp, hax_bv_decide]
def ne {α} (x y: α) [BEq α] : RustM Bool := pure (x != y)

@[simp, hax_bv_decide]
def lt {α} (x y: α) [(LT α)] [Decidable (x < y)] : RustM Bool := pure (x < y)

@[simp, hax_bv_decide]
def le {α} (x y: α) [(LE α)] [Decidable (x ≤ y)] : RustM Bool := pure (x ≤ y)

@[simp, hax_bv_decide]
def gt {α} (x y: α) [(LT α)] [Decidable (x > y)] : RustM Bool := pure (x > y)

@[simp, hax_bv_decide]
def ge {α} (x y: α) [(LE α)] [Decidable (x ≥ y)] : RustM Bool := pure (x ≥ y)

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

      @[spec]
      def eq_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ eq x y ⦃ ⇓ r => ⌜ r = (x.toInt == y.toInt) ⌝ ⦄ := by
        mvcgen [eq]; rw [← @Bool.coe_iff_coe]; simp [x.toInt_inj]

      @[spec]
      def ne_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ne x y ⦃ ⇓ r => ⌜ r = (x.toInt != y.toInt) ⌝ ⦄ := by
        mvcgen [ne]; rw [← @Bool.coe_iff_coe]; simp [x.toInt_inj]

      @[spec]
      def lt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ lt x y ⦃ ⇓ r => ⌜ r = decide (x.toInt < y.toInt) ⌝ ⦄ := by
        mvcgen [lt]; simp [x.lt_iff_toInt_lt]

      @[spec]
      def le_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ le x y ⦃ ⇓ r => ⌜ r = decide (x.toInt ≤ y.toInt) ⌝ ⦄ := by
        mvcgen [le]; simp [x.le_iff_toInt_le]

      @[spec]
      def gt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ gt x y ⦃ ⇓ r => ⌜ r = decide (x.toInt > y.toInt ) ⌝ ⦄ := by
        mvcgen [gt]; simp [y.lt_iff_toInt_lt]

      @[spec]
      def ge_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ge x y ⦃ ⇓ r => ⌜ r = decide (x.toInt ≥ y.toInt) ⌝ ⦄ := by
        mvcgen [ge]; simp [y.le_iff_toInt_le]

      end $typeName
    )
  else return ← `(
      namespace $typeName

      @[spec]
      def eq_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ eq x y ⦃ ⇓ r => ⌜ r = (x.toNat == y.toNat) ⌝ ⦄ := by
        mvcgen [eq]; rw [← @Bool.coe_iff_coe]; simp [x.toNat_inj]

      @[spec]
      def ne_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ ne x y ⦃ ⇓ r => ⌜ r = (x.toNat != y.toNat) ⌝ ⦄ := by
        mvcgen [ne]; rw [← @Bool.coe_iff_coe]; simp [x.toNat_inj]

      @[spec]
      def lt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ lt x y ⦃ ⇓ r => ⌜ r = decide (x.toNat < y.toNat) ⌝ ⦄ := by
        mvcgen [lt]

      @[spec]
      def le_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ le x y ⦃ ⇓ r => ⌜ r = decide (x.toNat ≤ y.toNat) ⌝ ⦄ := by
        mvcgen [le]

      @[spec]
      def gt_spec (x y : $typeName) : ⦃ ⌜ True ⌝ ⦄ gt x y ⦃ ⇓ r => ⌜ r = decide (x.toNat > y.toNat ) ⌝ ⦄ := by
        mvcgen [gt]

      @[spec]
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

end Rust_primitives.Hax.Machine_int

@[simp, spec, hax_bv_decide]
def CoreModels.Ops.Arith.Neg.neg {α} [Neg α] (x:α) : RustM α := pure (-x)

abbrev Core.Cmp.PartialEq.eq {α} [BEq α] (a b : α) := BEq.beq a b

set_option linter.unusedVariables false in
/-- Hax-generated bounded integers -/
abbrev Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
  (lo: usize) (hi: usize) := usize
--  {u : usize // lo ≤ u ∧ u ≤ hi}
-- TODO : make it into a proper subtype
