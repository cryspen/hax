/-
Hax Lean Backend - Cryspen

This library provides the Lean prelude for hax extracted rust-code. It contains
the lean definition of rust (and hax) primitives and intrinsics.

It borrows some definitions from the Aeneas project
(https://github.com/AeneasVerif/aeneas/)
-/

import Std
import Std.Do.Triple
import Std.Tactic.Do
import Std.Tactic.Do.Syntax
import Hax.BitVec

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-
# Monadic encoding

The encoding is based on the `Result` monad: all rust computations are wrapped
in the monad, representing the fact that they are not total.

-/

/--
  (Aeneas) Error cases
-/
inductive Error where
   | assertionFailure: Error
   | integerOverflow: Error
   | divisionByZero: Error
   | arrayOutOfBounds: Error
   | maximumSizeExceeded: Error
   | panic: Error
   | undef: Error
deriving Repr, BEq
open Error

/-- (Aeneas) Result monad, representing possible results of rust computations -/
inductive Result.{u} (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

namespace Result

@[simp]
instance instPure: Pure Result where
  pure x := .ok x

@[simp]
def bind (x: Result α) (f: α -> Result β) := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
def ofOption {α} (x:Option α) (e: Error) : Result α := match x with
  | .some v => pure v
  | .none => .fail e

@[simp]
instance instMonad : Monad Result where
  pure := pure
  bind := Result.bind

@[simp]
instance instLawfulMonad : LawfulMonad Result where
  id_map x := by
    dsimp [id, Functor.map]
    cases x;
    all_goals grind
  map_const := by
    intros α β
    dsimp [Functor.map, Functor.mapConst]
  seqLeft_eq x y := by
    dsimp [Functor.map, SeqLeft.seqLeft, Seq.seq]
    cases x ; all_goals cases y
    all_goals try simp
  seqRight_eq x y := by
    dsimp [Functor.map, SeqRight.seqRight, Seq.seq]
    cases x ; all_goals cases y
    all_goals try simp
  pure_seq g x := by
    dsimp [Functor.map, Seq.seq, pure]
  bind_pure_comp f x := by
    dsimp [Functor.map]
  bind_map f x := by
    dsimp [Functor.map, bind, pure, Seq.seq]
  pure_bind x f := by
    dsimp [pure, bind, pure]
  bind_assoc x f g := by
    dsimp [pure, bind]
    cases x; all_goals simp

@[simp]
instance instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (Pure.pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

@[simp]
instance instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, Pure.pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const, Bind.bind]

@[default_instance]
instance instCoe {α} : Coe α (Result α) where
  coe x := pure x

end Result


/-
  Logic predicates introduced by Hax (in pre/post conditions)
-/
section Logic

@[simp, spec]
abbrev hax_logical_op_and := (fun a b => a && b)
@[simp, spec]
abbrev hax_logical_op_or := (fun a b => a || b)

abbrev assert (b:Bool) : Result Unit :=
  if b then pure ()
  else .fail (Error.assertionFailure)

abbrev assume : Prop -> Result Unit := fun _ => pure ()

abbrev prop_constructors_from_bool (b :Bool) : Prop := (b = true)

end Logic

/-
  Integer types are represented as the corresponding type in Lean
-/
abbrev u8 := UInt8
abbrev u16 := UInt16
abbrev u32 := UInt32
abbrev u64 := UInt64
abbrev usize := USize
abbrev i8 := Int8
abbrev i16 := Int16
abbrev i32 := Int32
abbrev i64 := Int64
abbrev isize := ISize

/-- Class of objects that can be transformed into Nat -/
class ToNat (α: Type) where
  toNat : α -> Nat

@[simp]
instance : ToNat USize where
  toNat x := x.toNat
@[simp]
instance : ToNat u64 where
  toNat x := x.toNat
@[simp]
instance : ToNat u32 where
  toNat x := x.toNat
@[simp]
instance : ToNat u16 where
  toNat x := x.toNat
@[simp]
instance : ToNat Nat where
  toNat x := x

/-
  Coercions between integer types
-/
-- TODO : make sure all are necessary, document their use-cases
@[simp, spec]
instance : Coe i32 (Result i64) where
  coe x := pure (x.toInt64)

@[simp]
instance : Coe USize Nat where
  coe x := x.toNat

@[simp]
instance : Coe u32 Nat where
  coe x := x.toNat

@[simp]
instance : Coe Nat usize where
  coe x := USize.ofNat x

@[simp]
instance : Coe Nat i32 where
  coe x := Int32.ofNat x

@[simp]
instance : Coe USize UInt32 where
  coe x := x.toUInt32

@[simp]
instance : Coe USize (Result u32) where
  coe x := if x.toNat < UInt32.size then pure (x.toUInt32)
           else Result.fail .integerOverflow

@[simp]
instance {β} : Coe (α -> usize -> β) (α -> Nat -> β) where
  coe f a x := f a (USize.ofNat x)

@[simp]
instance {β} : Coe (α -> i32 -> β) (α -> Nat -> β) where
  coe f a x := f a (Int32.ofNat x)

@[simp]
instance : OfNat (Result Nat) n where
  ofNat := pure (n)


/-

# Arithmetic operations

The Rust arithmetic operations have their own notations, using a `?`. They
return a `Result`, that is `.fail` when arithmetic overflows occur.

-/
section Arithmetic

/-- The notation typeclass for homogeneous addition that returns a Result.  This
enables the notation `a +? b : α` where `a : α`, `b : α`. For now, there is no
heterogeneous version -/
class HaxAdd α where
  /-- `a +? b` computes the panicking sum of `a` and `b`.  The meaning of this
  notation is type-dependent. -/
  add : α → α → Result α

/-- The notation typeclass for homogeneous substraction that returns a Result.
This enables the notation `a -? b : α` where `a : α`, `b : α`. For now, there is
no heterogeneous version -/
class HaxSub α where
  /-- `a -? b` computes the panicking substraction of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  sub : α → α → Result α

/-- The notation typeclass for homogeneous multiplication that returns a Result.
This enables the notation `a *? b : Result α` where `a b : α`. For now, there is
no heterogeneous version -/
class HaxMul α where
  /-- `a -? b` computes the panicking multiplication of `a` and `b`.  The
  meaning of this notation is type-dependent. -/
  mul : α → α → Result α

/-- The notation typeclass for homogeneous division that returns a Result.  This
enables the notation `a /? b : Result α` where `a b : α`. For now, there is no
heterogeneous version -/
class HaxDiv α where
  /-- `a -? b` computes the panicking multiplication of `a` and `b`.  The
  meaning of this notation is type-dependent. -/
  div : α → α → Result α

/-- The typeclass behind the notation `a >>>? b : Result α` where `a b : α`. -/
class HaxShiftRight α where
  /-- `a >>>? b` computes the panicking right-shift of `a` by `b`.  The meaning
  of this notation is type-dependent. It panics if `b` exceeds the size of `a`.
  -/
  shiftRight : α → α → Result α

/-- The notation typeclass for remainder.  This enables the notation `a %? b :
Result α` where `a b : α`.  -/
class HaxRem α where
  /-- `a %? b` computes the panicking remainder upon dividing `a` by `b`.  The
  meaning of this notation is type-dependent. It panics if b is zero -/
  rem : α → α → Result α

@[inherit_doc] infixl:65 " +? "   => HaxAdd.add
@[inherit_doc] infixl:65 " -? "   => HaxSub.sub
@[inherit_doc] infixl:70 " *? "   => HaxMul.mul
@[inherit_doc] infixl:75 " >>>? " => HaxShiftRight.shiftRight
@[inherit_doc] infixl:70 " %? "   => HaxRem.rem
@[inherit_doc] infixl:70 " /? "   => HaxDiv.div
infixl:58 " ^^^? " => fun a b => pure (HXor.hXor a b)

/- Until notations are not introduced by the Lean backend, explicit hax-names
  are also provided -/
@[simp, spec]
def hax_machine_int_add {α} [HaxAdd α] (x y: α) : Result α := x +? y
@[simp, spec]
def hax_machine_int_sub {α} [HaxSub α] (x y: α) : Result α := x -? y
@[simp, spec]
def hax_machine_int_mul {α} [HaxMul α] (x y: α) : Result α := x *? y
@[simp, spec]
def hax_machine_int_div {α} [HaxDiv α] (x y: α) : Result α := x /? y
@[simp, spec]
def hax_machine_int_rem {α} [HaxRem α] (x y: α) : Result α := x %? y
@[simp, spec]
def hax_machine_int_shr {α} [HaxShiftRight α] (a b: α) : Result α := a >>>? b
@[simp, spec]
def hax_machine_int_bitxor {α} [HXor α α α] (a b: α) : Result α := a ^^^? b
@[simp]
def ops_arith_Neg_neg {α} [Neg α] (x:α) : Result α := pure (-x)

@[simp, spec]
def hax_machine_int_eq {α} (x y: α) [BEq α] : Result Bool := pure (x == y)
@[simp, spec]
def hax_machine_int_ne {α} (x y: α) [BEq α] : Result Bool := pure (x != y)
@[simp, spec]
def hax_machine_int_lt {α} (x y: α) [(LT α)] [Decidable (x < y)] : Result Bool :=
  pure (x < y)
@[simp, spec]
def hax_machine_int_le {α} (x y: α) [(LE α)] [Decidable (x ≤ y)] : Result Bool :=
  pure (x ≤ y)
@[simp, spec]
def hax_machine_int_gt {α} (x y: α) [(LT α)] [Decidable (x > y)] : Result Bool :=
  pure (x > y)
@[simp, spec]
def hax_machine_int_ge {α} (x y: α) [(LE α)] [Decidable (x ≥ y)] : Result Bool :=
  pure (x ≥ y)


/-

# Properties

For each integer types, instances of typeclasses for arithmetic operations are
given, along with hoare-triple specifications (to be used by mvcgen)

-/

namespace USize

/-- Partial addition on usize -/
instance instHaxAdd : HaxAdd USize where
  add x y :=
    if (BitVec.uaddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

/-- Partial substraction on usize -/
instance instHaxSub : HaxSub USize where
  sub x y :=
    if (BitVec.usubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

/-- Partial multiplication on usize -/
instance instHaxMul : HaxMul USize where
  mul x y :=
    if (BitVec.umulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

/-- Partial right shift on usize -/
instance instHaxShiftRight : HaxShiftRight USize where
  shiftRight x y :=
    if (y ≤ USize.size) then pure (x >>> y)
    else .fail .integerOverflow

/-- Partial division on usize. As it is unsigned, it only checks that the
divider is non-zero. -/
instance instHaxDiv : HaxDiv usize where
  div x y :=
    if y = 0 then .fail .divisionByZero
    else pure (x / y)

/-- Partial remainder on usize. As it is unsigned, it only checks that the
divider is non zero -/
instance instHaxRem : HaxRem usize where
  rem x y :=
    if y = 0 then .fail .divisionByZero
    else pure (x % y)

/- # Bitvec specifications -/

/-- Bitvec-based specification for rust addition on usize -/
theorem HaxAdd_spec_bv (x y: usize) :
  ¬ (BitVec.uaddOverflow x.toBitVec y.toBitVec) →
  ⦃ ⌜ True ⌝ ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by intros; mvcgen [instHaxAdd]

/-- Bitvec-based specification for rust multiplication on usize -/
theorem HaxMul_spec_bv (x y: usize) :
  ¬ (BitVec.umulOverflow x.toBitVec y.toBitVec) →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by intros; mvcgen [instHaxMul]

/-- Bitvec-based specification for rust substraction on usize -/
@[spec]
theorem HaxSub_spec_bv (x y: usize) :
  ¬ (BitVec.usubOverflow x.toBitVec y.toBitVec) →
  ⦃ ⌜ True ⌝ ⦄
  (x -? y)
  ⦃ ⇓ r => r = x - y ⦄ := by intros; mvcgen [instHaxSub]

/-- Bitvec-based specification for rust right-shift on usize -/
@[spec]
theorem HaxShiftRight_spec_bv (x y: usize) :
  y ≤ USize.size →
  ⦃ ⌜ True ⌝ ⦄
  ( x >>>? y)
  ⦃ ⇓ r => r = x >>> y ⦄ := by intros; mvcgen [instHaxShiftRight]

/-- Bitvec-based specification for rust division on usize -/
@[spec]
theorem HaxDiv_spec_bv (x y : usize) :
  y != 0 →
  ⦃ ⌜ True ⌝ ⦄
  ( x /? y)
  ⦃ ⇓ r => r = x / y ⦄
:= by intros; mvcgen [instHaxDiv] <;> simp <;> try grind

/-- Bitvec-based specification for rust remainder on usize  -/
@[spec]
theorem HaxRem_spec_bv (x y : usize) :
  y != 0 →
  ⦃ ⌜ True ⌝ ⦄
  ( x %? y)
  ⦃ ⇓ r => r = x % y ⦄
:= by intros; mvcgen [instHaxRem] <;> simp <;> try grind

namespace SpecBV
attribute [scoped spec] HaxAdd_spec_bv HaxSub_spec_bv HaxSub_spec_bv HaxSub_spec_bv HaxSub_spec_bv HaxSub_spec_bv
end SpecBV

/- # Nat specifications -/

/-- Nat-based specification for rust addition on usize -/
theorem HaxAdd_spec_nat (x y: usize) :
  x.toNat + y.toNat < size →
  ⦃ ⌜ True ⌝ ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by
  intros
  mvcgen [HaxAdd_spec_bv] ; simp
  apply eq_false_of_ne_true
  apply (BitVec.toNat_add_iff_not_uaddOverflow _).mp
  . simp [USize.toNat_toBitVec, size, Nat.mod_eq_iff_lt] at *; assumption
  . apply System.Platform.numBits_pos


/-- Nat-based specification for rust multiplication on usize -/
theorem HaxMul_spec_nat (x y: usize) :
  x.toNat * y.toNat < size →
  ⦃ ⌜ True ⌝ ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by
  intros
  mvcgen [HaxMul_spec_bv] ; simp
  apply eq_false_of_ne_true
  apply (BitVec.toNat_mul_iff_not_umulOverflow _).mp
  . simp [USize.toNat_toBitVec, size, Nat.mod_eq_iff_lt] at *; assumption
  . apply System.Platform.numBits_pos

namespace SpecNat
attribute [scoped spec] HaxAdd_spec_nat HaxMul_spec_nat
end SpecNat

end USize


namespace ISize

instance instHaxAdd : HaxAdd ISize where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

@[spec]
theorem HaxAdd_spec_bv (x y: isize) :
  ⦃ ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by mvcgen [instHaxAdd]

theorem HaxAdd_spec_bv_rw (x y: isize) :
   ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) →
   x +? y = Result.ok (x + y)
:= by simp [instHaxAdd]


instance instHaxSub : HaxSub ISize where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

@[spec]
theorem HaxSub_spec_bv (x y: isize) :
  ⦃ ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) ⦄
  (x -? y)
  ⦃ ⇓ r => r = x - y ⦄ := by mvcgen [instHaxSub]

instance instHaxMul : HaxMul ISize where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

@[spec]
theorem HaxMul_spec_bv (x y: isize) :
  ⦃ ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by mvcgen [instHaxMul]

instance instHaxShiftRight : HaxShiftRight ISize where
  shiftRight x y :=
    if (y ≤ ISize.size.toISize) then pure (x >>> y)
    else .fail .integerOverflow

@[spec]
theorem HaxShiftRight_spec_bv (x y: isize) :
  ⦃ y ≤ ISize.size.toISize ⦄
  ( x >>>? y)
  ⦃ ⇓ r => r = x >>> y ⦄ := by mvcgen [instHaxShiftRight]

end ISize


namespace Int64

instance instHaxAdd : HaxAdd Int64 where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

@[spec]
theorem HaxAdd_spec_bv (x y: i64) :
  ⦃ ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by mvcgen [instHaxAdd ]

instance instHaxSub : HaxSub Int64 where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

@[spec]
theorem HaxSub_spec_bv (x y: i64) :
  ⦃ ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) ⦄
  (x -? y)
  ⦃ ⇓ r => r = x - y ⦄ := by mvcgen [instHaxSub]

instance instHaxMul : HaxMul Int64 where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

@[spec]
theorem HaxMul_spec_bv (x y: i64) :
  ⦃ ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by mvcgen [instHaxMul]

instance instHaxShiftRight : HaxShiftRight Int64 where
  shiftRight x y :=
    if (y ≤ 64) then pure (x >>> y)
    else .fail .integerOverflow

@[spec]
theorem HaxShiftRight_spec_bv (x y: i64) :
  ⦃ y ≤ 64 ⦄
  ( x >>>? y)
  ⦃ ⇓ r => r = x >>> y ⦄ := by mvcgen [instHaxShiftRight]

end Int64


namespace Int32

instance instHaxAdd : HaxAdd Int32 where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

@[spec]
theorem HaxAdd_spec_bv (x y: i32) :
  ⦃ ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by mvcgen [instHaxAdd ]

theorem HaxAdd_spec_bv_rw (x y: i32) :
  ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) →
  x +? y = Result.ok (x + y) := by simp [instHaxAdd ] <;> grind

instance instHaxSub : HaxSub Int32 where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

@[spec]
theorem HaxSub_spec_bv (x y: i32) :
  ⦃ ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) ⦄
  (x -? y : Result i32)
  ⦃ ⇓ r => r = x - y ⦄ := by mvcgen [instHaxSub]

theorem HaxSub_spec_bv_rw (x y: i32) :
  ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) →
  x -? y = Result.ok (x - y) := by simp [instHaxSub ] <;> grind

instance instHaxMul : HaxMul Int32 where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

@[spec]
theorem HaxMul_spec_bv (x y: i32) :
  ⦃ ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) ⦄
  (x *? y : Result i32)
  ⦃ ⇓ r => r = x * y ⦄ := by mvcgen [instHaxMul]

instance instHaxRem : HaxRem i32 where
  rem x y :=
    if y = 0 then .fail .divisionByZero
    else if (BitVec.sdivOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x % y)

@[spec]
theorem HaxRem_spec_bv (x y : i32) :
  ⦃ y != 0 ∧ ¬ BitVec.sdivOverflow x.toBitVec y.toBitVec⦄
  ( x %? y)
  ⦃ ⇓ r => r = x % y ⦄ := by
  mvcgen [instHaxRem] <;> simp <;> try grind
  have ⟨ _ , h ⟩ := h
  apply h; assumption

@[simp]
theorem HaxRem_spec_bv_rw (x y : i32) :
  y != 0 →
  ¬ BitVec.sdivOverflow x.toBitVec y.toBitVec →
  x %? y = Result.ok (x % y)
:= by simp [instHaxRem] <;> try grind

end Int32

/-

# Wrapping operations

Rust also has total arithmetic operations, renamed by hax (with disambiguator)
for each implementation of typeclasses

-/

@[simp, spec]
def num__8_impl_wrapping_add (x y: u32) : Result u32 := pure (x + y)

@[simp, spec]
def num__8_impl_rotate_left (x: u32) (n: Nat) : Result u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n))


/-- Hax-generated bounded integers -/
abbrev hax__autogenerated_refinement__BoundedUsize_BoundedUsize
  (lo: USize) (hi: USize) := USize
--  {u : usize // lo ≤ u ∧ u ≤ hi}
-- Todo : make it into a proper subtype


def num__8_impl_from_le_bytes (x: Vector u8 4) : u32 :=
  x[0].toUInt32
  + (x[1].toUInt32 <<< 8)
  + (x[2].toUInt32 <<< 16)
  + (x[3].toUInt32 <<< 24)

def num__8_impl_to_le_bytes (x:u32) : Result (Vector u8 4) :=
  #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
  ]


end Arithmetic



/-

# Tuples

-/
section Tuples

abbrev hax_Tuple0 : Type := Unit
def constr_hax_Tuple0 : hax_Tuple0 := ()
instance : CoeDep Type hax_Tuple0 (hax_Tuple0) where
  coe := ()


abbrev hax_Tuple1 (α: Type) : Type := α × Unit
def constr_hax_Tuple1 {hax_Tuple1_Tuple0: α} : hax_Tuple1 α := (hax_Tuple1_Tuple0, ())

abbrev hax_Tuple2 (α β: Type) : Type := α × β
def constr_hax_Tuple2 {α β} {hax_Tuple2_Tuple0: α} {hax_Tuple2_Tuple1 : β} : hax_Tuple2 α β
  := (hax_Tuple2_Tuple0, hax_Tuple2_Tuple1)

end Tuples


/-

# Casts

-/
section Cast

/-- Hax-introduced explicit cast. It is partial (returns a `Result`) -/
@[simp, spec]
def convert_From_from {α β} [Coe α (Result β)] (x:α) : (Result β) := x

/-- Rust-supported casts on base types -/
class Cast (α β: Type) where
  cast : α → Result β

/-- Wrapping cast, does not fail on overflow -/
@[spec]
instance : Cast i64 i32 where
  cast x := pure (Int64.toInt32 x)

@[spec]
instance : Cast i64 (Result i32) where
  cast x := pure (x.toInt32)

@[spec]
instance : Cast usize u32 where
  cast x := pure (USize.toUInt32 x)

@[simp, spec]
def hax_cast_op {α β} [c: Cast α β] (x:α) : (Result β) := c.cast x

end Cast


/-

# Results

Not to be confused with the underlying `Result` monad of the Lean encoding, the
`result_Result` type models the rust `Result`.

-/
section RustResult

inductive result_Result α β
| ok : α -> result_Result α β
| err : β -> result_Result α β

instance {β : Type} : Monad (fun α => result_Result α β) where
  pure x := .ok x
  bind {α α'} x (f: α -> result_Result α' β) := match x with
  | .ok v => f v
  | .err e => .err e

/-- Rust unwrapping, panics if `x` is not `result_Result.ok _` -/
def result_impl_unwrap (α: Type) (β:Type) (x: result_Result α β) : (Result α) :=
  match x with
  | .ok v => pure v
  | .err _ => .fail .panic

end RustResult


/-

# Folds

Hax represents for-loops as folds over a range

-/
section Fold

/--

Hax-introduced function for for-loops, represented as a fold of the body of the
loop `body` from index `e` to `s`. If the invariant is not checked at runtime,
only passed around

-/
def hax_folds_fold_range {α}
  (s e : Nat)
  (inv : α -> Nat -> Result Bool)
  (init: α)
  (body : α -> Nat -> Result α) : Result α := do
  if e ≤ s then pure init
  else hax_folds_fold_range (s+1) e inv (← body init s) body

-- Lemma for proof of hax_folds_fold_range property
private
theorem induction_decreasing {e} {P: Nat  → Prop}
  (init: P e)
  (rec: ∀ n, n < e → P (n+1) → P n) :
  ∀ n, n ≤ e → P n
:= by
  intros n h
  by_cases (n = 0)
  . subst_vars
    induction e <;> try grind
  generalize h: (e - n) = d
  have : n = e - d := by omega
  have hlt : d < e := by omega
  rw [this] ; clear h this
  induction d with
  | zero => simp ; grind
  | succ d ih =>
    apply rec <;> try omega
    suffices e - (d + 1) + 1 = e - d by grind
    omega

-- Lemma for proof of hax_folds_fold_range property
private
def induction_decreasing_range {s e} {P: Nat → Nat → Prop} :
  s ≤ e →
  (init: P e e) →
  (rec: ∀ (n : Nat), n < e → s ≤ n → P (n + 1) e → P n e) →
  P s e
:= by intros; apply induction_decreasing (P := fun n => (s ≤ n → P n e)) (e := e) <;> try grind

/--

Nat-based specification for hax_folds_fold_range. It requires that the invariant
holds on the initial value, and that for any index `i` between the start and end
values, executing body of the loop on a value that satisfies the invariant
produces a result that also satisfies the invariant.

-/
@[spec]
theorem hax_folds_fold_range_spec {α}
  (s e : Nat)
  (inv : α -> Nat -> Result Bool)
  (init: α)
  (body : α -> Nat -> Result α) :
  ⦃ inv init s = pure true ∧
    s ≤ e ∧
    ∀ (acc:α) (i:Nat), s ≤ i → i < e →
             ⦃ inv acc i = pure true ⦄
             (body acc i)
             ⦃ ⇓ res => inv res (i+1) = pure true ⦄
  ⦄
  (hax_folds_fold_range s e inv init body)
  ⦃ ⇓ r => inv r e = pure true ⦄
:= by
  intro ⟨ h_inv_s, h_s_le_e , h_body ⟩
  revert h_inv_s init
  have :=  induction_decreasing_range (s := s) (e := e)
    (P := fun s e =>
      ∀ acc, inv acc s = pure true →
      wp⟦hax_folds_fold_range s e inv acc body⟧ ⇓ r => inv r e = pure true)
  apply this <;> clear this <;> try omega
  . simp [hax_folds_fold_range]
  . intros n _ _ ih acc h_acc
    unfold hax_folds_fold_range
    mvcgen <;> try grind
    specialize h_body acc n (by omega) (by omega)
    mspec h_body
    intro h_r
    apply (ih _ h_r)


end Fold

/-

# Arrays

Rust arrays, are represented as Lean `Vector` (Lean Arrays of known size)

-/
section Array

inductive array_TryFromSliceError where
  | array_TryFromSliceError

def hax_monomorphized_update_at_update_at_usize {α n}
  (a: Vector α n) (i:Nat) (v:α) : Result (Vector α n) :=
  if h: i < a.size then
    pure ( Vector.set a i v )
  else
    .fail (.arrayOutOfBounds)

@[spec]
def hax_update_at {α n} (m : Vector α n) (i : Nat) (v : α) : Result (Vector α n) :=
  if i < n then
    pure ( Vector.setIfInBounds m i v)
  else
    .fail (.arrayOutOfBounds)

@[spec]
def hax_repeat {α} (v:α) (n:Nat) : Result (Vector α n) :=
  pure (Vector.replicate n v)

def convert_TryInto_try_into {α n} (a: Array α) :
   Result (result_Result (Vector α n) array_TryFromSliceError) :=
   pure (
     if h: a.size = n then
       result_Result.ok (Eq.mp (congrArg _ h) a.toVector)
     else
       .err .array_TryFromSliceError
     )

end Array

/-

# Ranges

-/

/-- Type of ranges -/
inductive ops_range_Range (α: Type)  where
| range (r_start r_end : α) : ops_range_Range α

@[simp, spec]
def constr_ops_range_Range {α} (ops_range_Range_start : α) (ops_range_Range_end : α) :=
  ops_range_Range.range ops_range_Range_start ops_range_Range_end


/-

# Polymorphic index access

Hax introduces polymorphic index accesses, for any integer type (returning a
single value) and for ranges (returning an array of values). A typeclass-based
notation `a[i]_?` is introduced to support panicking lookups

-/
section Lookup

/--
The classes `GetElemResult` implement lookup notation `xs[i]_?`.
-/
class GetElemResult (coll : Type u) (idx : Type v) (elem : outParam (Type w)) where
  /--
  The syntax `arr[i]_?` gets the `i`'th element of the collection `arr`. It
  can panic if the index is out of bounds.
  -/
  getElemResult (xs : coll) (i : idx) : Result elem

export GetElemResult (getElemResult)

@[inherit_doc getElemResult]
syntax:max term noWs "[" withoutPosition(term) "]" noWs "_?": term
macro_rules | `($x[$i]_?) => `(getElemResult $x $i)

@[app_unexpander getElemResult] meta def unexpandGetElemResult : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index) => `($array[$index]_?)
  | _ => throw ()

/--

Until the backend introduces notations, a definition for the explicit name
`ops_index_index_index` is provided as a proxy

-/
@[simp, spec]
def ops_index_Index_index {α β γ} (a: α) (i:β) [GetElemResult α β γ] : (Result γ) := a[i]_?


instance Range.instGetElemResultArrayUSize :
  GetElemResult
    (Array α)
    (ops_range_Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ops_range_Range.range s e =>
    let size := xs.size;
    if s ≤ e && e ≤ size then
      pure ( xs.extract s e )
    else
      Result.fail Error.arrayOutOfBounds

instance Range.instGetElemResultVectorUSize :
  GetElemResult
    (Vector α n)
    (ops_range_Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ops_range_Range.range s e =>
    if s ≤ e && e ≤ n then
      pure (xs.extract s e).toArray
    else
      Result.fail Error.arrayOutOfBounds


instance USize.instGetElemResultArray {α} : GetElemResult (Array α) usize α where
  getElemResult xs i :=
    if h: i.toNat < xs.size then pure (xs[i])
    else .fail arrayOutOfBounds

instance USize.instGetElemResultVector {α n} : GetElemResult (Vector α n) usize α where
  getElemResult xs i :=
    if h: i.toNat < n then pure (xs[i.toNat])
    else .fail arrayOutOfBounds

instance Nat.instGetElemResultArray {α} : GetElemResult (Array α) Nat α where
  getElemResult xs i :=
    if h: i < xs.size then pure (xs[i])
    else .fail arrayOutOfBounds

instance Nat.instGetElemResultVector {α n} : GetElemResult (Vector α n) Nat α where
  getElemResult xs i :=
    if h: i < n then pure (xs[i])
    else .fail arrayOutOfBounds

@[spec]
theorem Nat.getElemArrayResult_spec
  (α : Type) (a: Array α) (i: Nat) (h: i < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i] ⦄ :=
  by mvcgen [Result.ofOption, Nat.instGetElemResultArray]

@[spec]
theorem Nat.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: Nat) (h : i < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i] ⦄ :=
  by mvcgen [Nat.instGetElemResultVector]

@[spec]
theorem USize.getElemArrayResult_spec
  (α : Type) (a: Array α) (i: usize) (h: i.toNat < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i.toNat]⦄ :=
  by mvcgen [USize.instGetElemResultArray]

@[spec]
theorem USize.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: usize) (h: i.toNat < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => r = a[i.toNat]⦄ :=
  by mvcgen [USize.instGetElemResultVector]

@[spec]
theorem Range.getElemArrayUSize_spec
  (α : Type) (a: Array α) (s e: usize) :
  s ≤ e →
  e ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(ops_range_Range.range s e)]_? )
  ⦃ ⇓ r => r = Array.extract a s e ⦄
:= by
  intros
  mvcgen [ops_index_Index_index, Range.instGetElemResultArrayUSize] <;> grind

@[spec]
theorem Range.getElemVectorUSize_spec
  (α : Type) (n: Nat) (a: Vector α n) (s e: usize) :
  s ≤ e →
  e ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(ops_range_Range.range s e)]_? )
  ⦃ ⇓ r => r = (Vector.extract a s e).toArray ⦄
:= by
  intros
  mvcgen [ops_index_Index_index, Range.instGetElemResultVectorUSize] <;> grind


end Lookup



/-

# Slices

Rust slices are represented as Lean Arrays (variable size)

-/


@[spec]
def unsize {α n} (a: Vector α n) : Result (Array α) :=
  pure (a.toArray)

def slice_impl_len α (a: Array α) : Result usize := pure a.size

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

def alloc_Global : Type := Unit
def vec_Vec (α: Type) (_Allocator:Type) : Type := Array α

def vec_impl_new (α: Type) (Allocator:Type) : Result (vec_Vec α Allocator) :=
  pure ((List.nil).toArray)

def vec__1_impl_len (α: Type) (Allocator:Type) (x: vec_Vec α Allocator) : Result Nat :=
  pure x.size

def vec__2_impl_extend_from_slice (α Allocator) (x: vec_Vec α Allocator) (y: Array α)
  : Result (vec_Vec α Allocator):=
  pure (x.append y)

def slice_impl_to_vec α (a:  Array α) : Result (vec_Vec α alloc_Global) :=
  pure a

-- For
instance {α n} : Coe (Array α) (Result (Vector α n)) where
  coe x :=
    if h: x.size = n then by
      rw [←h]
      apply pure
      apply (Array.toVector x)
    else .fail (.arrayOutOfBounds)

end RustVectors



/-

# Closures

Rust closures are represented as regular Lean functions. Yet, Rust uses a
typeclass `Fn` when calling a closure, which uncurrifies the arguments. This is
taken care of by the `Fn` class

-/

class Fn α (β : outParam Type) γ where
  call : α → β → γ

instance {α β} : Fn (α → β) (hax_Tuple1 α) β where
  call f x := f x.fst

instance {α β γ} : Fn (α → β → γ) (hax_Tuple2 α β) γ where
  call f x := f x.fst x.snd

def ops_function_Fn_call {α β γ} [Fn α β γ] (f: α) (x: β) : γ := Fn.call f x


-- Miscellaneous
def ops_deref_Deref_deref {α Allocator} (v: vec_Vec α Allocator)
  : Result (Array α)
  := pure v


-- Tactics
macro "hax_bv_decide" : tactic => `(tactic| (
  any_goals (injections <;> subst_vars)
  all_goals try (
    simp [Int32.eq_iff_toBitVec_eq,
          Int32.lt_iff_toBitVec_slt,
          Int32.le_iff_toBitVec_sle,
          Int64.eq_iff_toBitVec_eq,
          Int64.lt_iff_toBitVec_slt,
          Int64.le_iff_toBitVec_sle] at * <;>
    bv_decide;
    done
 )))
