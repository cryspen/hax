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
import Hax.Initialize

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-
# Monadic encoding

The encoding is based on the `RustM` monad: all rust computations are wrapped
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
deriving Repr, BEq, DecidableEq
open Error

/--
  RustM monad (corresponding to Aeneas's `Result` monad), representing
  possible results of rust computations
-/
inductive RustM.{u} (α : Type u) where
  | ok (v: α): RustM α
  | fail (e: Error): RustM α
  | div
deriving Repr, BEq, DecidableEq

namespace RustM

@[simp, hax_bv_decide]
instance instPure: Pure RustM where
  pure x := .ok x

@[simp]
def bind {α β : Type} (x: RustM α) (f: α -> RustM β) := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

@[simp]
def ofOption {α} (x:Option α) (e: Error) : RustM α := match x with
  | .some v => pure v
  | .none => .fail e

@[reducible]
def isOk {α : Type} (x: RustM α) : Bool := match x with
| .ok _ => true
| _ => false

@[reducible, hax_bv_decide]
def of_isOk {α : Type} (x: RustM α) (h: RustM.isOk x): α :=
  match x with
  | .ok v => v

@[simp, spec]
def ok_of_isOk {α : Type} (v : α) (h: isOk (ok v)): (ok v).of_isOk h = v := by rfl

@[simp, hax_bv_decide]
instance instMonad : Monad RustM where
  pure := pure
  bind := RustM.bind

@[simp]
instance instLawfulMonad : LawfulMonad RustM where
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
instance instWP : WP RustM (.except Error .pure) where
  wp x := match x with
  | .ok v => wp (Pure.pure v : Except Error _)
  | .fail e => wp (throw e : Except Error _)
  | .div => PredTrans.const ⌜False⌝

@[simp]
instance instWPMonad : WPMonad RustM (.except Error .pure) where
  wp_pure := by intros; ext Q; simp [wp, PredTrans.pure, Pure.pure, Except.pure, Id.run]
  wp_bind x f := by
    simp only [instWP]
    ext Q
    cases x <;> simp [PredTrans.bind, PredTrans.const, Bind.bind]

@[default_instance]
instance instCoe {α} : Coe α (RustM α) where
  coe x := pure x

@[simp, spec, default_instance]
instance {α} : Coe (RustM (RustM α)) (RustM α) where
  coe x := match x with
  | .ok y => y
  | .fail e => .fail e
  | .div => .div


end RustM


/-
  Logic predicates introduced by Hax (in pre/post conditions)
-/
section Logic

namespace Rust_primitives.Hax.Logical_op

/-- Boolean conjunction. Cannot panic (always returns .ok ) -/
@[simp, spec, hax_bv_decide]
def and (a b: Bool) : RustM Bool := pure (a && b)

/-- Boolean disjunction. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def or (a b: Bool) : RustM Bool := pure (a || b)

/-- Boolean negation. Cannot panic (always returns .ok )-/
@[simp, spec, hax_bv_decide]
def not (a :Bool) : RustM Bool := pure (!a)

@[inherit_doc] infixl:35 " &&? " => and
@[inherit_doc] infixl:30 " ||? " => or
@[inherit_doc] notation:max "!?" b:40 => not b

end Rust_primitives.Hax.Logical_op

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
  coe x := USize.ofNat x

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

infixl:58 " ^^^? " => fun a b => pure (HXor.hXor a b)
infixl:60 " &&&? " => fun a b => pure (HAnd.hAnd a b)

/- Until notations are not introduced by the Lean backend, explicit hax-names
  are also provided -/
namespace Rust_primitives.Hax.Machine_int

@[simp, spec, hax_bv_decide]
def eq {α} (x y: α) [BEq α] : RustM Bool := pure (x == y)
@[simp, spec, hax_bv_decide]
def ne {α} (x y: α) [BEq α] : RustM Bool := pure (x != y)
@[simp, spec, hax_bv_decide]
def lt {α} (x y: α) [(LT α)] [Decidable (x < y)] : RustM Bool :=
  pure (x < y)
@[simp, spec, hax_bv_decide]
def le {α} (x y: α) [(LE α)] [Decidable (x ≤ y)] : RustM Bool :=
  pure (x ≤ y)
@[simp, spec, hax_bv_decide]
def gt {α} (x y: α) [(LT α)] [Decidable (x > y)] : RustM Bool :=
  pure (x > y)
@[simp, spec, hax_bv_decide]
def ge {α} (x y: α) [(LE α)] [Decidable (x ≥ y)] : RustM Bool :=
  pure (x ≥ y)

end Rust_primitives.Hax.Machine_int

@[simp, spec, hax_bv_decide]
def Rust_primitives.Arithmetic.neg {α} [Neg α] (x:α) : RustM α := pure (-x)


/-

# Wrapping operations

Rust also has total arithmetic operations, renamed by hax (with disambiguator)
for each implementation of typeclasses

-/

namespace Core.Num.Impl_8
@[simp, spec]
def wrapping_add (x y: u32) : RustM u32 := pure (x + y)

@[simp, spec]
def rotate_left (x: u32) (n: Nat) : RustM u32 :=
  pure (UInt32.ofBitVec (BitVec.rotateLeft x.toBitVec n))

@[simp, spec]
def from_le_bytes (x: Vector u8 4) : u32 :=
  x[0].toUInt32
  + (x[1].toUInt32 <<< 8)
  + (x[2].toUInt32 <<< 16)
  + (x[3].toUInt32 <<< 24)

@[simp, spec]
def to_le_bytes (x:u32) : RustM (Vector u8 4) :=
  #v[
    (x % 256).toUInt8,
    (x >>> 8 % 256).toUInt8,
    (x >>> 16 % 256).toUInt8,
    (x >>> 24 % 256).toUInt8,
  ]

end Core.Num.Impl_8



/-- Hax-generated bounded integers -/
abbrev Hax_bounded_integers.Hax__autogenerated_refinement__BoundedUsize.BoundedUsize
  (lo: usize) (hi: usize) := usize
--  {u : usize // lo ≤ u ∧ u ≤ hi}
-- Todo : make it into a proper subtype



/-

# Tuples

-/
section Tuples
namespace Rust_primitives.Hax

structure Tuple0 where

structure Tuple1 (α0: Type) where
  _0 : α0

structure Tuple2 (α0 α1: Type) where
  _0 : α0
  _1 : α1

structure Tuple3 (α0 α1 α2: Type) where
  _0 : α0
  _1 : α1
  _2 : α2

structure Tuple4 (α0 α1 α2 α3 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3

structure Tuple5 (α0 α1 α2 α3 α4 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4

structure Tuple6 (α0 α1 α2 α3 α4 α5 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5

structure Tuple7 (α0 α1 α2 α3 α4 α5 α6 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6

structure Tuple8 (α0 α1 α2 α3 α4 α5 α6 α7 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7

structure Tuple9 (α0 α1 α2 α3 α4 α5 α6 α7 α8 α9 : Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7
  _8 : α8

structure Tuple10 (α0 α1 α2 α3 α4 α5 α6 α7 α8 α9: Type) where
  _0 : α0
  _1 : α1
  _2 : α2
  _3 : α3
  _4 : α4
  _5 : α5
  _6 : α6
  _7 : α7
  _8 : α8
  _9 : α9

end Rust_primitives.Hax
end Tuples

open Rust_primitives.Hax


/-

# Casts

-/
section Cast

/-- Hax-introduced explicit cast. It is partial (returns a `RustM`) -/
@[simp, spec, hax_bv_decide]
def Core.Convert.From.from (β α) [Coe α (RustM β)] (x:α) : (RustM β) := x

/-- Rust-supported casts on base types -/
class Cast (α β: Type) where
  cast : α → RustM β

attribute [hax_bv_decide] Cast.cast

/-- Wrapping cast, does not fail on overflow -/
@[spec]
instance : Cast i64 i32 where
  cast x := pure (Int64.toInt32 x)

@[spec]
instance : Cast i64 (RustM i32) where
  cast x := pure (x.toInt32)

@[spec]
instance : Cast usize u32 where
  cast x := pure (USize.toUInt32 x)

@[spec]
instance : Cast String String where
  cast x := pure x

@[simp, spec, hax_bv_decide]
def Rust_primitives.Hax.cast_op {α β} [c: Cast α β] (x:α) : (RustM β) := c.cast x

end Cast


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

inductive Core.Ops.Control_flow.ControlFlow (α β: Type 0) where
| Break (x: α)
| Continue (y : β)
open Core.Ops.Control_flow

class Rust_primitives.Hax.Folds {int_type: Type} where
  fold_range {α : Type}
    (s e : int_type)
    (inv : α -> int_type -> RustM Bool)
    (init: α)
    (body : α -> int_type -> RustM α)
    : RustM α
  fold_range_return  {α_acc α_ret : Type}
    (s e: int_type)
    (inv : α_acc -> int_type -> RustM Bool)
    (init: α_acc)
    (body : α_acc -> int_type ->
      RustM (ControlFlow (ControlFlow α_ret (Tuple2 Tuple0 α_acc)) α_acc ))
    : RustM (ControlFlow α_ret α_acc)

instance : Coe Nat Nat where
  coe x := x

@[simp]
instance {α} [Coe α Nat] [Coe Nat α]: @Rust_primitives.Hax.Folds α where
  fold_range s e inv init body := do
    let mut acc := init
    for i in [s:e] do
      acc := (← body acc i)
    return acc

  fold_range_return {α_acc α_ret} s e inv init body := do
    let mut acc := init
    for i in [s:e] do
      match (← body acc i) with
      | .Break (.Break res ) => return (.Break res)
      | .Break (.Continue ⟨ ⟨ ⟩, res⟩) => return (.Continue res)
      | .Continue acc' => acc := acc'
    pure (ControlFlow.Continue acc)

/-
Nat-based specification for hax_folds_fold_range. It requires that the invariant
holds on the initial value, and that for any index `i` between the start and end
values, executing body of the loop on a value that satisfies the invariant
produces a result that also satisfies the invariant.

-/
@[spec]
theorem Rust_primitives.Hax.Folds.fold_range_spec {α}
  (s e : Nat)
  (inv : α -> Nat -> RustM Bool)
  (init: α)
  (body : α -> Nat -> RustM α) :
  s ≤ e →
  inv init s = pure true →
  (∀ (acc:α) (i:Nat),
    s ≤ i →
    i < e →
    inv acc i = pure true →
    ⦃ ⌜ True ⌝ ⦄
    (body acc i)
    ⦃ ⇓ res => ⌜ inv res (i+1) = pure true ⌝ ⦄) →
  ⦃ ⌜ True ⌝ ⦄
  (Rust_primitives.Hax.Folds.fold_range s e inv init body)
  ⦃ ⇓ r => ⌜ inv r e = pure true ⌝ ⦄
:= by
  intro h_inv_s h_le h_body
  mvcgen [Spec.forIn_list, fold_range]
  case inv1 =>
    simp [Coe.coe]
    exact (⇓ (⟨ suff, _, _ ⟩ , acc ) => ⌜ inv acc (s + suff.length) = pure true ⌝ )
  case vc1.step _ x _ h_list _ h =>
    intros
    simp [Coe.coe] at h_list h
    simp [Std.Range.toList] at h_list
    have ⟨k ,⟨ h_k, h_pre, h_suff⟩⟩ := List.range'_eq_append_iff.mp h_list
    let h_suff := Eq.symm h_suff
    let ⟨ h_x ,_ , h_suff⟩ := List.range'_eq_cons_iff.mp h_suff
    mstart ; mspec h_body <;> simp [Coe.coe] at * <;> try grind
  case vc2.pre | vc4.post.except =>
    simp [Coe.coe] at * <;> try assumption
  case vc3.post.success =>
    simp at *
    suffices (s + (e - s)) = e by (rw [← this]; assumption)
    omega


@[spec]
theorem Rust_primitives.Hax.Folds.usize.fold_range_spec {α}
  (s e : usize)
  (inv : α -> usize -> RustM Bool)
  (init: α)
  (body : α -> usize -> RustM α) :
  s ≤ e →
  inv init s = pure true →
  (∀ (acc:α) (i:usize),
    s ≤ i →
    i < e →
    inv acc i = pure true →
    ⦃ ⌜ True ⌝ ⦄
    (body acc i)
    ⦃ ⇓ res => ⌜ inv res (i+1) = pure true ⌝ ⦄) →
  ⦃ ⌜ True ⌝ ⦄
  (Rust_primitives.Hax.Folds.fold_range s e inv init body)
  ⦃ ⇓ r => ⌜ inv r e = pure true ⌝ ⦄
:= by
  intro h_inv_s h_le h_body
  have : s.toNat < USize.size := by apply USize.toNat_lt_size
  have : e.toNat < USize.size := by apply USize.toNat_lt_size
  mvcgen [Spec.forIn_list, fold_range]
  case inv1 =>
    simp [Coe.coe]
    exact (⇓ (⟨ suff, _, _ ⟩ , acc ) => ⌜ inv acc (s + (USize.ofNat suff.length)) = pure true ⌝ )
  case vc2.pre | vc4.post.except =>
    simp [Coe.coe, USize.ofNat] at * <;> try assumption
  case vc3.post.success =>
    simp at *
    suffices (s + USize.ofNat (USize.toNat e - USize.toNat s)) = e by rwa [← this]
    rw [USize.ofNat_sub, USize.ofNat_toNat, USize.ofNat_toNat] <;> try assumption
    rw (occs := [2])[← USize.sub_add_cancel (b := s) (a := e)]
    rw [USize.add_comm]
  case vc1.step _ x _ h_list _ h =>
    intros
    simp [Coe.coe] at h_list h
    simp [Std.Range.toList] at h_list
    have ⟨k ,⟨ h_k, h_pre, h_suff⟩⟩ := List.range'_eq_append_iff.mp h_list
    let h_suff := Eq.symm h_suff
    let ⟨ h_x ,_ , h_suff⟩ := List.range'_eq_cons_iff.mp h_suff
    unfold USize.size at *
    mstart ; mspec h_body <;> simp [Coe.coe] at * <;> (try grind) <;> (try omega)
    . apply USize.le_iff_toNat_le.mpr
      rw [← h_x, USize.toNat_ofNat', Nat.mod_eq_of_lt] <;> try omega
    . apply USize.lt_iff_toNat_lt.mpr
      rw [← h_x, USize.toNat_ofNat', Nat.mod_eq_of_lt] <;> try omega
    . rw [← h_x, USize.ofNat_add, USize.ofNat_toNat]
      rwa [h_pre, List.length_range'] at h
    . rw [h_pre, List.length_range', ← h_x, USize.ofNat_add, USize.ofNat_toNat, USize.add_assoc]
      intro; assumption


end Fold

/-

# Arrays

Rust arrays, are represented as Lean `Vector` (Lean Arrays of known size)

-/
section RustArray


abbrev RustArray := Vector


inductive Core.Array.TryFromSliceError where
  | array.TryFromSliceError

def Rust_primitives.Hax.Monomorphized_update_at.update_at_usize {α n}
  (a: Vector α n) (i:Nat) (v:α) : RustM (Vector α n) :=
  if h: i < a.size then
    pure ( Vector.set a i v )
  else
    .fail (.arrayOutOfBounds)

@[spec]
theorem Rust_primitives.Hax.Monomorphized_update_at.update_at_usize.spec
  {α n} (a: Vector α n) (i:Nat) (v:α) (h: i < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize a i v)
  ⦃ ⇓ r => ⌜ r = Vector.set a i v ⌝ ⦄ := by
  mvcgen [Rust_primitives.Hax.Monomorphized_update_at.update_at_usize]


@[spec]
def Rust_primitives.Hax.update_at {α n} (m : Vector α n) (i : Nat) (v : α) : RustM (Vector α n) :=
  if i < n then
    pure ( Vector.setIfInBounds m i v)
  else
    .fail (.arrayOutOfBounds)

@[spec]
def Rust_primitives.Hax.repeat
  {α int_type: Type}
  {n: Nat} [ToNat int_type]
  (v:α) (size:int_type) : RustM (Vector α n)
  :=
  if (n = ToNat.toNat size) then
    pure (Vector.replicate n v)
  else
    .fail Error.arrayOutOfBounds

end RustArray

/-

# Ranges

-/

/-- Type of ranges -/
structure Core.Ops.Range.Range (α: Type) where
  start : α
  _end : α

open Core.Ops.Range

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
class GetElemResult (coll : Type) (idx : Type) (elem : outParam (Type)) where
  /--
  The syntax `arr[i]_?` gets the `i`'th element of the collection `arr`. It
  can panic if the index is out of bounds.
  -/
  getElemResult (xs : coll) (i : idx) : RustM elem

export GetElemResult (getElemResult)

@[inherit_doc getElemResult]
syntax:max term noWs "[" withoutPosition(term) "]" noWs "_?": term
macro_rules | `($x[$i]_?) => `(getElemResult $x $i)

-- Have lean use the notation when printing
@[app_unexpander getElemResult] meta def unexpandGetElemResult : Lean.PrettyPrinter.Unexpander
  | `($_ $array $index) => `($array[$index]_?)
  | _ => throw ()

/--

Until the backend introduces notations, a definition for the explicit name
`ops.index_index_index` is provided as a proxy

-/
@[simp, spec]
def Core.Ops.Index.Index.index {α β γ} (a: α) (i:β) [GetElemResult α β γ] : (RustM γ) := a[i]_?


instance Range.instGetElemResultArrayUSize {α: Type}:
  GetElemResult
    (Array α)
    (Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    let size := xs.size;
    if s ≤ e && e ≤ size then
      pure ( xs.extract s e )
    else
      RustM.fail Error.arrayOutOfBounds

instance Range.instGetElemResultVectorUSize {α : Type} {n : Nat} :
  GetElemResult
    (Vector α n)
    (Range usize)
    (Array α) where
  getElemResult xs i := match i with
  | ⟨s, e⟩ =>
    if s ≤ e && e ≤ n then
      pure (xs.extract s e).toArray
    else
      RustM.fail Error.arrayOutOfBounds


instance usize.instGetElemResultArray {α} : GetElemResult (Array α) usize α where
  getElemResult xs i :=
    if h: i.toNat < xs.size then pure (xs[i])
    else .fail arrayOutOfBounds

instance usize.instGetElemResultVector {α n} : GetElemResult (Vector α n) usize α where
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
  ⦃ ⇓ r => ⌜ r = a[i] ⌝ ⦄ :=
  by mvcgen [RustM.ofOption, Nat.instGetElemResultArray]

@[spec]
theorem Nat.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: Nat) (h : i < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a[i] ⌝ ⦄ :=
  by mvcgen [Nat.instGetElemResultVector]

@[spec]
theorem usize.getElemArrayResult_spec
  (α : Type) (a: Array α) (i: usize) (h: i.toNat < a.size) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a[i.toNat] ⌝ ⦄ :=
  by mvcgen [usize.instGetElemResultArray]

@[spec]
theorem usize.getElemVectorResult_spec
  (α : Type) (n:Nat) (a: Vector α n) (i: usize) (h: i.toNat < n) :
  ⦃ ⌜ True ⌝ ⦄
  ( a[i]_? )
  ⦃ ⇓ r => ⌜ r = a[i.toNat] ⌝ ⦄ :=
  by mvcgen [usize.instGetElemResultVector]

@[spec]
theorem Range.getElemArrayUSize_spec
  (α : Type) (a: Array α) (s e: usize) :
  s ≤ e →
  e ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = Array.extract a s e ⌝ ⦄
:= by
  intros
  mvcgen [Core.Ops.Index.Index.index, Range.instGetElemResultArrayUSize] ; grind

@[spec]
theorem Range.getElemVectorUSize_spec
  (α : Type) (n: Nat) (a: Vector α n) (s e: usize) :
  s ≤ e →
  e ≤ a.size →
  ⦃ ⌜ True ⌝ ⦄
  ( a[(Range.mk s e)]_? )
  ⦃ ⇓ r => ⌜ r = (Vector.extract a s e).toArray ⌝ ⦄
:= by
  intros
  mvcgen [Core.Ops.Index.Index.index, Range.instGetElemResultVectorUSize] ; grind


end Lookup



/-

# Slices

Rust slices are represented as Lean Arrays (variable size)

-/


@[spec]
def Rust_primitives.unsize {α n} (a: Vector α n) : RustM (Array α) :=
  pure (a.toArray)

@[simp, spec]
def Core.Slice.Impl.len α (a: Array α) : RustM usize := pure a.size

/-

# Vectors

Rust vectors are represented as Lean Arrays (variable size)

-/
section RustVectors

abbrev RustSlice := Array
abbrev RustVector := Array

def Alloc.Alloc.Global : Type := Unit

abbrev Alloc.Vec.Vec (α: Type) (_Allocator:Type) : Type := Array α

def Alloc.Vec.Impl.new (α: Type) (_:Tuple0) : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure ((List.nil).toArray)

def Alloc.Vec.Impl_1.len (α: Type) (_Allocator: Type) (x: Alloc.Vec.Vec α Alloc.Alloc.Global) : RustM usize :=
  pure x.size

def Alloc.Vec.Impl_2.extend_from_slice α (_Allocator: Type) (x: Alloc.Vec.Vec α Alloc.Alloc.Global) (y: Array α)
  : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global):=
  pure (x.append y)

def Alloc.Slice.Impl.to_vec α (a:  Array α) : RustM (Alloc.Vec.Vec α Alloc.Alloc.Global) :=
  pure a

-- For
instance {α n} : Coe (Array α) (RustM (Vector α n)) where
  coe x :=
    if h: x.size = n then by
      rw [←h]
      apply pure
      apply (Array.toVector x)
    else .fail (.arrayOutOfBounds)

end RustVectors


/-

# BV_Decide Lemmas

In the following, we define an encoding of the entire `RustM` monad so that we can run `bv_decide`
on equalities between `RustM` values.

-/

/-- We encode `RustM` values into the following structure to be able to run `bv_decide`: -/
structure BVRustM (α : Type) where
  ok : Bool
  val : α
  err : BitVec 3

/-- Encodes `RustM` values into `BVRustM` to be able to run `bv_decide`. -/
def RustM.toBVRustM {α} [Inhabited α] : RustM α → BVRustM α
| ok v                      => ⟨ true, v, 0 ⟩
| fail .assertionFailure    => ⟨ false, default, 0 ⟩
| fail .integerOverflow     => ⟨ false, default, 1 ⟩
| fail .divisionByZero      => ⟨ false, default, 2 ⟩
| fail .arrayOutOfBounds    => ⟨ false, default, 3 ⟩
| fail .maximumSizeExceeded => ⟨ false, default, 4 ⟩
| fail .panic               => ⟨ false, default, 5 ⟩
| fail .undef               => ⟨ false, default, 6 ⟩
| div                       => ⟨ false, default, 7 ⟩

attribute [hax_bv_decide] Coe.coe

@[hax_bv_decide] theorem RustM.toBVRustM_ok {α} [Inhabited α] {v : α} :
    (RustM.ok v).toBVRustM = ⟨ true, v, 0 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_assertionFailure {α} [Inhabited α] :
    (RustM.fail .assertionFailure : RustM α).toBVRustM = ⟨ false, default, 0 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_integerOverflow {α} [Inhabited α] :
    (RustM.fail .integerOverflow : RustM α).toBVRustM = ⟨ false, default, 1 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_divisionByZero {α} [Inhabited α] :
    (RustM.fail .divisionByZero : RustM α).toBVRustM = ⟨ false, default, 2 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_arrayOutOfBounds {α} [Inhabited α] :
    (RustM.fail .arrayOutOfBounds : RustM α).toBVRustM = ⟨ false, default, 3 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_maximumSizeExceeded {α} [Inhabited α] :
    (RustM.fail .maximumSizeExceeded: RustM α).toBVRustM = ⟨ false, default, 4 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_panic {α} [Inhabited α] :
    (RustM.fail .panic : RustM α).toBVRustM = ⟨ false, default, 5 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_undef {α} [Inhabited α] :
    (RustM.fail .undef : RustM α).toBVRustM = ⟨ false, default, 6 ⟩ := rfl
@[hax_bv_decide] theorem RustM.toBVRustM_div {α} [Inhabited α] :
    (RustM.div : RustM α ).toBVRustM = ⟨ false, default, 7 ⟩ := rfl

@[hax_bv_decide]
theorem RustM.toBVRustM_ite {α} [Inhabited α] {c : Prop} [Decidable c]  (x y : RustM α) :
    (if c then x else y).toBVRustM = (if c then x.toBVRustM else y.toBVRustM) := by grind

@[hax_bv_decide]
theorem RustM.beq_iff_toBVRustM_eq {α} [Inhabited α] [DecidableEq α] (x y : RustM α) :
    decide (x = y) =
      (x.toBVRustM.ok == y.toBVRustM.ok &&
       x.toBVRustM.val == y.toBVRustM.val &&
       x.toBVRustM.err == y.toBVRustM.err) := by
  by_cases h : x = y
  · simp [h]
  · revert h
    cases x using RustM.toBVRustM.match_1 <;>
    cases y using RustM.toBVRustM.match_1 <;>
    grind [toBVRustM]

@[hax_bv_decide]
theorem RustM.toBVRustM_bind {α β} [Inhabited α] [Inhabited β] (x : RustM α) (f : α → RustM β) :
  (x.bind f).toBVRustM =
    if x.toBVRustM.ok
    then (f x.toBVRustM.val).toBVRustM
    else {x.toBVRustM with val := default} := by
  apply RustM.toBVRustM.match_1.splitter _ x <;> simp [bind, toBVRustM]

@[hax_bv_decide]
theorem RustM.Triple_iff_BitVec {α} [Inhabited α]
    (a : Prop) [Decidable a] (b : α → Prop) (x : RustM α) [Decidable (b x.toBVRustM.val)] :
    ⦃ ⌜ a ⌝ ⦄ x ⦃ ⇓ r => ⌜ b r ⌝ ⦄ ↔
      (!decide a || (x.toBVRustM.ok && decide (b x.toBVRustM.val))) := by
  cases x using RustM.toBVRustM.match_1 <;>
    by_cases a <;> simp [Triple, RustM.toBVRustM, Decidable.imp_iff_not_or]

/-- This lemma is used to make some variants of `>>>?` accessible for `bv_decide` -/
@[hax_bv_decide]
theorem Int32.to_Int64_toNatClampNeg : (Int32.toNatClampNeg 1).toInt64 = 1 := rfl

/-

# Specs

-/

structure Spec {α}
    (requires : RustM Prop)
    (ensures : α → RustM Prop)
    (f : RustM α) where
  pureRequires : {p : Prop // ⦃ ⌜ True ⌝ ⦄ requires ⦃ ⇓r => ⌜ r = p ⌝ ⦄}
  pureEnsures : {p : α → Prop // pureRequires.val → ∀ a, ⦃ ⌜ True ⌝ ⦄ ensures a ⦃ ⇓r => ⌜ r = p a ⌝ ⦄}
  contract : ⦃ ⌜ pureRequires.val ⌝ ⦄ f ⦃ ⇓r => ⌜ pureEnsures.val r ⌝ ⦄

-- Miscellaneous
def Core.Ops.Deref.Deref.deref {α Allocator} (β : Type) (v: Alloc.Vec.Vec α Allocator)
  : RustM (Array α)
  := pure v

abbrev string_indirection : Type := String
abbrev Alloc.String.String : Type := string_indirection

abbrev Alloc.Boxed.Box (T _Allocator : Type) := T

-- Assume, Assert

namespace Hax_lib

abbrev assert (b:Bool) : RustM Tuple0 :=
  if b then pure ⟨ ⟩
  else .fail (Error.assertionFailure)

abbrev assume : Prop -> RustM Tuple0 := fun _ => pure ⟨ ⟩

abbrev Prop.Constructors.from_bool (b :Bool) : Prop := (b = true)

end Hax_lib
