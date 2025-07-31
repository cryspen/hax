-- This library provides a monadic encoding over Hax primitives
import Std
import Std.Do.Triple
import Std.Tactic.Do
import Std.Tactic.Do.Syntax

open Std.Do
open Std.Tactic

-- Aeneas errors
-- see https://github.com/AeneasVerif/aeneas/
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

inductive Result.{u} (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div
deriving Repr, BEq

@[simp]
instance Result.instPure: Pure Result where
  pure x := .ok x

@[simp, spec]
def Result.pure (x: α) : Result α := (Result.instPure.pure x)

@[simp]
def Result.bind (x: Result α) (f: α -> Result β) := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
def Result.ofOption {α} (x:Option α) (e: Error) : Result α := match x with
  | .some v => pure v
  | .none => .fail e

@[simp]
instance Result.instMonad : Monad Result where
  pure := pure
  bind := Result.bind

@[simp]
instance Result.instLawfulMonad : LawfulMonad Result where
  id_map x := by
    dsimp [id, Functor.map, Result.pure]
    cases x;
    all_goals grind
  map_const := by
    intros α β
    dsimp [Functor.map, Functor.mapConst]
  seqLeft_eq x y := by
    dsimp [Functor.map, SeqLeft.seqLeft, Seq.seq, Result.pure]
    cases x ; all_goals cases y
    all_goals try simp
  seqRight_eq x y := by
    dsimp [Functor.map, SeqRight.seqRight, Seq.seq, Result.pure]
    cases x ; all_goals cases y
    all_goals try simp
  pure_seq g x := by
    dsimp [Functor.map, Seq.seq, pure, Result.pure]
  bind_pure_comp f x := by
    dsimp [Functor.map]
  bind_map f x := by
    dsimp [Functor.map, bind, pure, Seq.seq, Result.pure]
  pure_bind x f := by
    dsimp [pure, bind, Result.pure]
  bind_assoc x f g := by
    dsimp [pure, bind]
    cases x; all_goals simp

-- set_option pp.coercions false
@[simp]
instance Result.instWP : WP Result (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (Pure.pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

-- set_option pp.raw true
@[simp]
instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, Pure.pure, Except.pure, Id.run, Result.pure]
  wp_bind x f := by
    simp only [instWP]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const, Bind.bind]

@[default_instance]
instance Result.instCoe {α} : Coe α (Result α) where
  coe x := pure x

-- Logic
abbrev hax_logical_op_and := (fun a b => a && b)
abbrev hax_logical_op_or := (fun a b => a || b)

-- Integer types

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

class ToNat (α: Type) where
  toNat : α -> Nat

-- should use a macro here
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

@[simp, spec]
instance : Coe i32 (Result i64) where
  coe x := pure (x.toInt64)

@[simp]
instance : Coe u32 Nat where
  coe x := x.toNat

@[simp]
instance : Coe Nat usize where
  coe x := USize.ofNat x

@[simp]
instance : Coe USize UInt32 where
  coe x := x.toUInt32

@[simp]
instance : Coe USize (Result u32) where
  coe x := if h: x.toNat < UInt32.size then pure (x.toUInt32)
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


-- Arithmetic
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

@[inherit_doc] infixl:65 " +? " => HaxAdd.add
@[inherit_doc] infixl:65 " -? " => HaxSub.sub
@[inherit_doc] infixl:70 " *? " => HaxMul.mul
@[inherit_doc] infixl:75 " >>>? " => HaxShiftRight.shiftRight
@[inherit_doc] infixl:70 " %? "   => HaxRem.rem
@[inherit_doc] infixl:70 " /? "   => HaxDiv.div

-- Overflowing operations
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
@[simp]
def hax_machine_int_bitxor {α} [Xor α] (a b: α) : Result α := Result.pure (a ^^^ b)
@[simp]
def ops_arith_Neg_neg {α} [Neg α] (x:α) : Result α := pure (-x)

@[simp]
def hax_machine_int_eq {α} (x y: α) [BEq α] : Result Bool := pure (x == y)
@[simp]
def hax_machine_int_ne {α} (x y: α) [BEq α] : Result Bool := pure (x != y)
@[simp]
def hax_machine_int_lt {α} (x y: α) [(LT α)] [Decidable (x < y)] : Result Bool := pure (x < y)
@[simp]
def hax_machine_int_le {α} (x y: α) [(LE α)] [Decidable (x ≤ y)] : Result Bool := pure (x ≤ y)
@[simp]
def hax_machine_int_gt {α} (x y: α) [(LE α)] [Decidable (x ≥ y)] : Result Bool := pure (x ≥ y)
@[simp]
def hax_machine_int_ge {α} (x y: α) [(LT α)] [Decidable (x > y)] : Result Bool := pure (x > y)



namespace USize

instance instHaxAdd : HaxAdd USize where
  add x y :=
    if (BitVec.saddOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x + y)

@[spec]
theorem HaxAdd_spec_bv (x y: usize) :
  ⦃ ¬ (BitVec.saddOverflow x.toBitVec y.toBitVec) ⦄
  (x +? y)
  ⦃ ⇓ r => r = x + y ⦄ := by mvcgen [instHaxAdd ]

instance instHaxSub : HaxSub USize where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

@[spec]
theorem HaxSub_spec_bv (x y: usize) :
  ⦃ ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) ⦄
  (x -? y)
  ⦃ ⇓ r => r = x - y ⦄ := by mvcgen [instHaxSub]

instance instHaxMul : HaxMul USize where
  mul x y :=
    if (BitVec.smulOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x * y)

@[spec]
theorem HaxMul_spec_bv (x y: usize) :
  ⦃ ¬ (BitVec.smulOverflow x.toBitVec y.toBitVec) ⦄
  (x *? y)
  ⦃ ⇓ r => r = x * y ⦄ := by mvcgen [instHaxMul]

instance instHaxShiftRight : HaxShiftRight USize where
  shiftRight x y :=
    if (y ≤ USize.size) then pure (x >>> y)
    else .fail .integerOverflow

@[spec]
theorem HaxShiftRight_spec_bv (x y: usize) :
  ⦃ y ≤ USize.size ⦄
  ( x >>>? y)
  ⦃ ⇓ r => r = x >>> y ⦄ := by mvcgen [instHaxShiftRight]

instance instHaxDiv : HaxDiv usize where
  div x y :=
    if y = 0 then .fail .divisionByZero
    else if (BitVec.sdivOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x / y)

@[spec]
theorem HaxDiv_spec_bv (x y : usize) :
  ⦃ y != 0 ∧ ¬ BitVec.sdivOverflow x.toBitVec y.toBitVec⦄
  ( x /? y)
  ⦃ ⇓ r => r = x / y ⦄ := by
  mvcgen [instHaxDiv] <;> simp <;> try grind
  have ⟨ _ , h ⟩ := h
  apply h; assumption

instance instHaxRem : HaxRem usize where
  rem x y :=
    if y = 0 then .fail .divisionByZero
    else if (BitVec.sdivOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x % y)

@[spec]
theorem HaxRem_spec_bv (x y : usize) :
  ⦃ y != 0 ∧ ¬ BitVec.sdivOverflow x.toBitVec y.toBitVec⦄
  ( x %? y)
  ⦃ ⇓ r => r = x % y ⦄ := by
  mvcgen [instHaxRem] <;> simp <;> try grind
  have ⟨ _ , h ⟩ := h
  apply h; assumption


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
  ⦃ ⇓ r => r = x + y ⦄ := by mvcgen [instHaxAdd ]

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

-- @[spec]
-- theorem HaxAdd_spec_Int (x y: i32) :
--   ⦃ x.toInt + y.toInt < Int32.maxValue.toInt ⦄
--   (x +? y : Result i32)
--   ⦃ ⇓ r => r = x + y ⦄
-- := by
--   mvcgen [Int32.instHaxAdd ]
--   cases h__overflow : ((toBitVec x).saddOverflow (toBitVec y)) <;> try simp
--   have := @BitVec.toInt_add_of_not_saddOverflow _ (x.toBitVec) (y.toBitVec)
--   simp []

instance instHaxSub : HaxSub Int32 where
  sub x y :=
    if (BitVec.ssubOverflow x.toBitVec y.toBitVec) then .fail .integerOverflow
    else pure (x - y)

@[spec]
theorem HaxSub_spec_bv (x y: i32) :
  ⦃ ¬ (BitVec.ssubOverflow x.toBitVec y.toBitVec) ⦄
  (x -? y : Result i32)
  ⦃ ⇓ r => r = x - y ⦄ := by mvcgen [instHaxSub]

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

end Int32


abbrev hax__autogenerated_refinement__BoundedUsize_BoundedUsize
  (lo: USize) (hi: USize) := USize
--  {u : usize // lo ≤ u ∧ u ≤ hi}

-- #check hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 19
-- #check fun (x: {usize // True}) => x.val

set_option pp.coercions false

-- instance {n lo hi : Nat} {hlo: lo ≤ x} {hhi: x ≤ hi}:
--   OfNat (hax__autogenerated_refinement__BoundedUsize_BoundedUsize lo hi) x where
--   ofNat := {
--     val := x ,
--     property := by
--       constructor
--       . unfold Nat.cast

--         apply USize.le_iff_toNat_le.mp

--       . apply USize.le_iff_toNat_le.mp
--         grind

--   }
-- #check (10: hax__autogenerated_refinement__BoundedUsize_BoundedUsize 0 10)

-- Wrapping operations
@[simp, spec]
def num_8_impl_wrapping_add (x y: u32) : Result u32 := pure (x + y)

@[simp]
def num_8_impl_rotate_left (x: u32) (n: Nat) : Result u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n))

end Arithmetic

-- Tuples

def hax_Tuple0 : Type := Unit
def constr_hax_Tuple0 : hax_Tuple0 := ()
instance : Coe hax_Tuple0 Unit where
  coe _ := ()


def hax_Tuple1 (α: Type) : Type := α × Unit
def constr_hax_Tuple1 {hax_Tuple1_Tuple0: α} : hax_Tuple1 α := (hax_Tuple1_Tuple0, ())

def hax_Tuple2 (α β: Type) : Type := α × β
def constr_hax_Tuple2 {α β} {hax_Tuple2_Tuple0: α} {hax_Tuple2_Tuple1 : β} : hax_Tuple2 α β
  := (hax_Tuple2_Tuple0, hax_Tuple2_Tuple1)



-- Nums
-- TO remove once name display is fixed

def num_8_impl_from_le_bytes (x: Vector u8 n) : u32 := (0: u32) -- TOFIX

-- Casts
@[simp, spec]
def convert_From_from {α β} [Coe α (Result β)] (x:α) : (Result β) := x

class Cast (α β: Type) where
  cast : α → Result β

@[spec]
instance : Cast i64 i32 where
  cast x := pure (Int64.toInt32 x)

@[spec]
instance : Cast usize u32 where
  cast x := pure (USize.toUInt32 x)

@[simp, spec]
def hax_cast_op {α β} [c: Cast α β] (x:α) : (Result β) := c.cast x

-- Results
inductive result_Result α β
| ok : α -> result_Result α β
| err : β -> result_Result α β

instance {β : Type} : Monad (fun α => result_Result α β) where
  pure x := .ok x
  bind {α α'} x (f: α -> result_Result α' β) := match x with
  | .ok v => f v
  | .err e => .err e

inductive array_TryFromSliceError where
  | array_TryFromSliceError

-- Assert
def assert (b:Bool) : Result Unit :=
  if b then pure ()
  else .fail (Error.assertionFailure)

def assume : Prop -> Result Unit := fun _ => pure ()
def prop_constructors_from_bool (b :Bool) : Prop := (b = true)

-- Hax

-- To extend with invariants
def hax_folds_fold_range {α}
  (s e : Nat)
  (_inv : α -> Nat -> Result Bool)
  (init: α)
  (f : α -> Nat -> Result α) : Result α :=
  Array.foldlM f init (Array.range e) s e

-- Arrays

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


def result_impl_unwrap (α: Type) (β:Type) (x: result_Result α β) : (Result α) :=
  match x with
  | .ok v => pure v
  | .err _ => .fail .panic

-- Vectors
def hax_repeat {α} (v:α) (n:Nat) : Result (Vector α n) :=
  pure (Eq.mp (congrArg (Vector α) (@Array.size_replicate α n v))
    (Array.replicate n v).toVector)

-- Ranges

inductive ops_range_Range (α: Type)  where
| constr_ops_range_Range
  {ops_range_Range_start: α}
  {ops_range_Range_end: α} : ops_range_Range α

def constr_ops_range_Range {α} {ops_range_Range_start : α} {ops_range_Range_end : α} :=
  ops_range_Range.constr_ops_range_Range
    (ops_range_Range_start := ops_range_Range_start)
    (ops_range_Range_end := ops_range_Range_end)

def ops_index_Index_index {α β γ} (a: α) (i:β)
  [GetElem α β (Result γ) (fun _ _ => True) ] : (Result γ) := a[i]

instance :
  GetElem
    (Array α)
    (ops_range_Range usize)
    (Result (Array α)) (fun _ _ => True) where
  getElem xs i _ := match i with
  | @ops_range_Range.constr_ops_range_Range _ s e =>
    let size := xs.size;
    if (s > e || e > size || s > size) then
      Result.fail Error.arrayOutOfBounds
    else
      pure ( xs.extract s e )

instance {α n} [tn: ToNat β]:
  GetElem
    (Vector α n)
    (ops_range_Range β)
    (Result (Array α)) (fun _ _ => True) where
  getElem xs i _ := match i with
  | @ops_range_Range.constr_ops_range_Range _ s e =>
    let e := tn.toNat e;
    let s := tn.toNat s;
    let size := xs.size;
    if (s > e || e > size || s > size) then
      Result.fail Error.arrayOutOfBounds
    else
      pure ( (Vector.extract xs s e ).toArray)

instance GetElemResult [tn: ToNat β] : GetElem (Array α) β (Result α) (fun _ _ => True) where
  getElem xs i _ := Result.ofOption (xs[tn.toNat i]?) .arrayOutOfBounds

instance USize.instGetElemArrayResult {α} : GetElem (Array α) (usize) (Result α) (fun _ _ => True) :=
  GetElemResult

instance : GetElem (Array α) Nat (Result α) (fun _ _ => True) :=
  GetElemResult

@[simp]
instance {α β : Type} {n : Nat} [tn: ToNat β]: GetElem (Vector α n) β (Result α) (fun _ _ => True) where
  getElem xs i _ := Result.ofOption (xs[tn.toNat i]?) .arrayOutOfBounds

@[simp]
instance {α : Type} {n : Nat}: GetElem (Vector α n) Nat (Result α) (fun _ _ => True) where
  getElem xs i _ := Result.ofOption xs[i]? .arrayOutOfBounds

-- Arrays
section Arrays

def convert_TryInto_try_into {α n} (a: Array α) :
   Result (result_Result (Vector α n) array_TryFromSliceError) :=
   pure (
     if h: a.size = n then
       result_Result.ok (Eq.mp (congrArg _ h) a.toVector)
     else
       .err .array_TryFromSliceError
     )

end Arrays

-- Slices
def alloc_Global : Type := Unit

@[spec]
def unsize {α n} (a: Vector α n) : Result (Array α) :=
  pure (a.toArray)

def slice_impl_len α (a: Array α) : Result usize := pure a.size
def vec_Vec (α: Type) (_Allocator:Type) : Type := Array α

def vec_impl_new (α: Type) (Allocator:Type) : Result (vec_Vec α Allocator) :=
  pure ((List.nil).toArray)

def vec_1_impl_len (α: Type) (Allocator:Type) (x: vec_Vec α Allocator) : Result Nat :=
  pure x.size

def vec_2_impl_extend_from_slice (α Allocator) (x: vec_Vec α Allocator) (y: Array α)
  : Result (vec_Vec α Allocator):=
  pure (x.append y)

def slice_impl_to_vec α (a:  Array α) : Result (vec_Vec α alloc_Global) :=
  pure a

-- For
instance {α n} : Coe (Array α) (Result (Vector α n)) where
  coe x :=
    if h: x.size = n then by
      rw [←h]
      apply Result.pure
      apply (Array.toVector x)
    else .fail (.arrayOutOfBounds)


-- Bytes
def num_8_impl_to_le_bytes (_:u32) : Result (Vector u8 4) := pure (#v[0, 0, 0, 0]) -- TOFIX


-- Closures
def ops_function_Fn_call {α β} (f: α -> β) (x: α) := f x


-- Miscellaneous
def ops_deref_Deref_deref {α Allocator} (v: vec_Vec α Allocator)
  : Result (Array α)
  := pure v
