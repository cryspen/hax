
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax.core_models.prologue
import Hax.Tactic.HaxSpec
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace core_models.array

structure TryFromSliceError where
  -- no fields

@[spec]
def Impl_23.as_slice (T : Type) (N : usize) (s : (RustArray T N)) :
    RustM (RustSlice T) := do
  (rust_primitives.slice.array_as_slice T (N) s)

end core_models.array


namespace core_models.array.iter

structure IntoIter (T : Type) (N : usize) where
  _0 : (rust_primitives.sequence.Seq T)

end core_models.array.iter


namespace core_models.borrow

class Borrow.AssociatedTypes (Self : Type) (Borrowed : Type) where

class Borrow (Self : Type) (Borrowed : Type)
  [associatedTypes : outParam (Borrow.AssociatedTypes (Self : Type) (Borrowed :
      Type))]
  where
  borrow (Self) (Borrowed) : (Self -> RustM Borrowed)

end core_models.borrow


namespace core_models.clone

class Clone.AssociatedTypes (Self : Type) where

class Clone (Self : Type)
  [associatedTypes : outParam (Clone.AssociatedTypes (Self : Type))]
  where
  clone (Self) : (Self -> RustM Self)

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Clone.AssociatedTypes T
  where

instance Impl (T : Type) : Clone T where
  clone := fun (self : T) => do (pure self)

end core_models.clone


namespace core_models.cmp

class PartialEq.AssociatedTypes (Self : Type) (Rhs : Type) where

class PartialEq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialEq.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  eq (Self) (Rhs) : (Self -> Rhs -> RustM Bool)

class Eq.AssociatedTypes (Self : Type) where
  [trait_constr_Eq_i0 : PartialEq.AssociatedTypes Self Self]

attribute [instance] Eq.AssociatedTypes.trait_constr_Eq_i0

class Eq (Self : Type)
  [associatedTypes : outParam (Eq.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Eq_i0 : PartialEq Self Self]

attribute [instance] Eq.trait_constr_Eq_i0

inductive Ordering : Type
| Less : Ordering
| Equal : Ordering
| Greater : Ordering

def Ordering.Less.AnonConst : isize := (-1 : isize)

def Ordering.Equal.AnonConst : isize := (0 : isize)

def Ordering.Greater.AnonConst : isize := (1 : isize)

@[spec]
def Ordering_cast_to_repr (x : Ordering) : RustM isize := do
  match x with
    | (Ordering.Less ) => do (pure Ordering.Less.AnonConst)
    | (Ordering.Equal ) => do (pure Ordering.Equal.AnonConst)
    | (Ordering.Greater ) => do (pure Ordering.Greater.AnonConst)

class Neq.AssociatedTypes (Self : Type) (Rhs : Type) where

class Neq (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Neq.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  neq (Self) (Rhs) : (Self -> Rhs -> RustM Bool)

@[reducible] instance Impl.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_i0 : PartialEq T T ] :
  Neq.AssociatedTypes T T
  where

instance Impl
  (T : Type)
  [trait_constr_Impl_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_i0 : PartialEq T T ] :
  Neq T T
  where
  neq := fun (self : T) (y : T) => do ((← (PartialEq.eq T T self y)) ==? false)

structure Reverse (T : Type) where
  _0 : T

@[reducible] instance Impl_3.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_3_i0 : PartialEq T T ] :
  PartialEq.AssociatedTypes (Reverse T) (Reverse T)
  where

instance Impl_3
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 : PartialEq.AssociatedTypes T T]
  [trait_constr_Impl_3_i0 : PartialEq T T ] :
  PartialEq (Reverse T) (Reverse T)
  where
  eq := fun (self : (Reverse T)) (other : (Reverse T)) => do
    (PartialEq.eq T T (Reverse._0 other) (Reverse._0 self))

@[reducible] instance Impl_4.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 : Eq.AssociatedTypes T]
  [trait_constr_Impl_4_i0 : Eq T ] :
  Eq.AssociatedTypes (Reverse T)
  where

instance Impl_4
  (T : Type)
  [trait_constr_Impl_4_associated_type_i0 : Eq.AssociatedTypes T]
  [trait_constr_Impl_4_i0 : Eq T ] :
  Eq (Reverse T)
  where

@[reducible] instance Impl_6.AssociatedTypes :
  PartialEq.AssociatedTypes u8 u8
  where

instance Impl_6 : PartialEq u8 u8 where
  eq := fun (self : u8) (other : u8) => do (self ==? other)

@[reducible] instance Impl_7.AssociatedTypes : Eq.AssociatedTypes u8 where

instance Impl_7 : Eq u8 where

@[reducible] instance Impl_8.AssociatedTypes :
  PartialEq.AssociatedTypes i8 i8
  where

instance Impl_8 : PartialEq i8 i8 where
  eq := fun (self : i8) (other : i8) => do (self ==? other)

@[reducible] instance Impl_9.AssociatedTypes : Eq.AssociatedTypes i8 where

instance Impl_9 : Eq i8 where

@[reducible] instance Impl_10.AssociatedTypes :
  PartialEq.AssociatedTypes u16 u16
  where

instance Impl_10 : PartialEq u16 u16 where
  eq := fun (self : u16) (other : u16) => do (self ==? other)

@[reducible] instance Impl_11.AssociatedTypes : Eq.AssociatedTypes u16 where

instance Impl_11 : Eq u16 where

@[reducible] instance Impl_12.AssociatedTypes :
  PartialEq.AssociatedTypes i16 i16
  where

instance Impl_12 : PartialEq i16 i16 where
  eq := fun (self : i16) (other : i16) => do (self ==? other)

@[reducible] instance Impl_13.AssociatedTypes : Eq.AssociatedTypes i16 where

instance Impl_13 : Eq i16 where

@[reducible] instance Impl_14.AssociatedTypes :
  PartialEq.AssociatedTypes u32 u32
  where

instance Impl_14 : PartialEq u32 u32 where
  eq := fun (self : u32) (other : u32) => do (self ==? other)

@[reducible] instance Impl_15.AssociatedTypes : Eq.AssociatedTypes u32 where

instance Impl_15 : Eq u32 where

@[reducible] instance Impl_16.AssociatedTypes :
  PartialEq.AssociatedTypes i32 i32
  where

instance Impl_16 : PartialEq i32 i32 where
  eq := fun (self : i32) (other : i32) => do (self ==? other)

@[reducible] instance Impl_17.AssociatedTypes : Eq.AssociatedTypes i32 where

instance Impl_17 : Eq i32 where

@[reducible] instance Impl_18.AssociatedTypes :
  PartialEq.AssociatedTypes u64 u64
  where

instance Impl_18 : PartialEq u64 u64 where
  eq := fun (self : u64) (other : u64) => do (self ==? other)

@[reducible] instance Impl_19.AssociatedTypes : Eq.AssociatedTypes u64 where

instance Impl_19 : Eq u64 where

@[reducible] instance Impl_20.AssociatedTypes :
  PartialEq.AssociatedTypes i64 i64
  where

instance Impl_20 : PartialEq i64 i64 where
  eq := fun (self : i64) (other : i64) => do (self ==? other)

@[reducible] instance Impl_21.AssociatedTypes : Eq.AssociatedTypes i64 where

instance Impl_21 : Eq i64 where

@[reducible] instance Impl_22.AssociatedTypes :
  PartialEq.AssociatedTypes u128 u128
  where

instance Impl_22 : PartialEq u128 u128 where
  eq := fun (self : u128) (other : u128) => do (self ==? other)

@[reducible] instance Impl_23.AssociatedTypes : Eq.AssociatedTypes u128 where

instance Impl_23 : Eq u128 where

@[reducible] instance Impl_24.AssociatedTypes :
  PartialEq.AssociatedTypes i128 i128
  where

instance Impl_24 : PartialEq i128 i128 where
  eq := fun (self : i128) (other : i128) => do (self ==? other)

@[reducible] instance Impl_25.AssociatedTypes : Eq.AssociatedTypes i128 where

instance Impl_25 : Eq i128 where

@[reducible] instance Impl_26.AssociatedTypes :
  PartialEq.AssociatedTypes usize usize
  where

instance Impl_26 : PartialEq usize usize where
  eq := fun (self : usize) (other : usize) => do (self ==? other)

@[reducible] instance Impl_27.AssociatedTypes : Eq.AssociatedTypes usize where

instance Impl_27 : Eq usize where

@[reducible] instance Impl_28.AssociatedTypes :
  PartialEq.AssociatedTypes isize isize
  where

instance Impl_28 : PartialEq isize isize where
  eq := fun (self : isize) (other : isize) => do (self ==? other)

@[reducible] instance Impl_29.AssociatedTypes : Eq.AssociatedTypes isize where

instance Impl_29 : Eq isize where

end core_models.cmp


namespace core_models.convert

class Into.AssociatedTypes (Self : Type) (T : Type) where

class Into (Self : Type) (T : Type)
  [associatedTypes : outParam (Into.AssociatedTypes (Self : Type) (T : Type))]
  where
  into (Self) (T) : (Self -> RustM T)

class From.AssociatedTypes (Self : Type) (T : Type) where

class From (Self : Type) (T : Type)
  [associatedTypes : outParam (From.AssociatedTypes (Self : Type) (T : Type))]
  where
  _from (Self) (T) : (T -> RustM Self)

@[reducible] instance Impl.AssociatedTypes
  (T : Type)
  (U : Type)
  [trait_constr_Impl_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_i0 : From U T ] :
  Into.AssociatedTypes T U
  where

instance Impl
  (T : Type)
  (U : Type)
  [trait_constr_Impl_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_i0 : From U T ] :
  Into T U
  where
  into := fun (self : T) => do (From._from U T self)

structure Infallible where
  -- no fields

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  From.AssociatedTypes T T
  where

instance Impl_3 (T : Type) : From T T where
  _from := fun (x : T) => do (pure x)

class AsRef.AssociatedTypes (Self : Type) (T : Type) where

class AsRef (Self : Type) (T : Type)
  [associatedTypes : outParam (AsRef.AssociatedTypes (Self : Type) (T : Type))]
  where
  as_ref (Self) (T) : (Self -> RustM T)

@[reducible] instance Impl_4.AssociatedTypes (T : Type) :
  AsRef.AssociatedTypes T T
  where

instance Impl_4 (T : Type) : AsRef T T where
  as_ref := fun (self : T) => do (pure self)

end core_models.convert


namespace core_models.default

class Default.AssociatedTypes (Self : Type) where

class Default (Self : Type)
  [associatedTypes : outParam (Default.AssociatedTypes (Self : Type))]
  where
  default (Self) : (rust_primitives.hax.Tuple0 -> RustM Self)

end core_models.default


namespace core_models.f32

opaque Impl.abs (x : f64) : RustM f64

end core_models.f32


namespace core_models.fmt

structure Error where
  -- no fields

structure Formatter where
  -- no fields

structure Arguments where
  _0 : rust_primitives.hax.Tuple0

end core_models.fmt


namespace core_models.fmt.rt

opaque ArgumentType : Type

structure Argument where
  ty : ArgumentType

opaque Impl.new_display (T : Type) (x : T) : RustM Argument

opaque Impl.new_debug (T : Type) (x : T) : RustM Argument

opaque Impl.new_lower_hex (T : Type) (x : T) : RustM Argument

opaque Impl_1.new_binary (T : Type) (x : T) : RustM Argument

opaque Impl_1.new_const (T : Type) (U : Type) (x : T) (y : U) :
    RustM core_models.fmt.Arguments

opaque Impl_1.new_v1 (T : Type) (U : Type) (V : Type) (W : Type)
    (x : T)
    (y : U)
    (z : V)
    (t : W) :
    RustM core_models.fmt.Arguments

@[spec]
def Impl_1.none (_ : rust_primitives.hax.Tuple0) :
    RustM (RustArray Argument 0) := do
  (pure #v[])

opaque Impl_1.new_v1_formatted (T : Type) (U : Type) (V : Type)
    (x : T)
    (y : U)
    (z : V) :
    RustM core_models.fmt.Arguments

inductive Count : Type
| Is : u16 -> Count
| Param : u16 -> Count
| Implied : Count

structure Placeholder where
  position : usize
  flags : u32
  precision : Count
  width : Count

structure UnsafeArg where
  -- no fields

end core_models.fmt.rt


namespace core_models.hash

class Hasher.AssociatedTypes (Self : Type) where

class Hasher (Self : Type)
  [associatedTypes : outParam (Hasher.AssociatedTypes (Self : Type))]
  where

class Hash.AssociatedTypes (Self : Type) where

class Hash (Self : Type)
  [associatedTypes : outParam (Hash.AssociatedTypes (Self : Type))]
  where
  hash (Self)
    (H : Type)
    [trait_constr_hash_associated_type_i1 : Hasher.AssociatedTypes H]
    [trait_constr_hash_i1 : Hasher H ] :
    (Self -> H -> RustM H)

end core_models.hash


namespace core_models.hint

def black_box (T : Type) (dummy : T) : RustM T := do (pure dummy)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def black_box.spec (T : Type) (dummy : T) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (hax_lib.prop.Impl.from_bool true))
      (black_box (T : Type) (dummy : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [black_box] <;> bv_decide
}

def must_use (T : Type) (value : T) : RustM T := do (pure value)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def must_use.spec (T : Type) (value : T) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (hax_lib.prop.Impl.from_bool true))
      (must_use (T : Type) (value : T)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [must_use] <;> bv_decide
}

end core_models.hint


namespace core_models.iter.adapters.enumerate

structure Enumerate (I : Type) where
  iter : I
  count : usize

@[spec]
def Impl.new (I : Type) (iter : I) : RustM (Enumerate I) := do
  (pure (Enumerate.mk (iter := iter) (count := (0 : usize))))

end core_models.iter.adapters.enumerate


namespace core_models.iter.adapters.step_by

structure StepBy (I : Type) where
  iter : I
  step : usize

@[spec]
def Impl.new (I : Type) (iter : I) (step : usize) : RustM (StepBy I) := do
  (pure (StepBy.mk (iter := iter) (step := step)))

end core_models.iter.adapters.step_by


namespace core_models.iter.adapters.map

structure Map (I : Type) (F : Type) where
  iter : I
  f : F

@[spec]
def Impl.new (I : Type) (F : Type) (iter : I) (f : F) : RustM (Map I F) := do
  (pure (Map.mk (iter := iter) (f := f)))

end core_models.iter.adapters.map


namespace core_models.iter.adapters.take

structure Take (I : Type) where
  iter : I
  n : usize

@[spec]
def Impl.new (I : Type) (iter : I) (n : usize) : RustM (Take I) := do
  (pure (Take.mk (iter := iter) (n := n)))

end core_models.iter.adapters.take


namespace core_models.iter.adapters.zip

structure Zip (I1 : Type) (I2 : Type) where
  it1 : I1
  it2 : I2

end core_models.iter.adapters.zip


namespace core_models.marker

class Copy.AssociatedTypes (Self : Type) where
  [trait_constr_Copy_i0 : core_models.clone.Clone.AssociatedTypes Self]

attribute [instance] Copy.AssociatedTypes.trait_constr_Copy_i0

class Copy (Self : Type)
  [associatedTypes : outParam (Copy.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Copy_i0 : core_models.clone.Clone Self]

attribute [instance] Copy.trait_constr_Copy_i0

class Send.AssociatedTypes (Self : Type) where

class Send (Self : Type)
  [associatedTypes : outParam (Send.AssociatedTypes (Self : Type))]
  where

class Sync.AssociatedTypes (Self : Type) where

class Sync (Self : Type)
  [associatedTypes : outParam (Sync.AssociatedTypes (Self : Type))]
  where

class Sized.AssociatedTypes (Self : Type) where

class Sized (Self : Type)
  [associatedTypes : outParam (Sized.AssociatedTypes (Self : Type))]
  where

class StructuralPartialEq.AssociatedTypes (Self : Type) where

class StructuralPartialEq (Self : Type)
  [associatedTypes : outParam (StructuralPartialEq.AssociatedTypes (Self :
      Type))]
  where

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Send.AssociatedTypes T
  where

instance Impl (T : Type) : Send T where

@[reducible] instance Impl_1.AssociatedTypes (T : Type) :
  Sync.AssociatedTypes T
  where

instance Impl_1 (T : Type) : Sync T where

@[reducible] instance Impl_2.AssociatedTypes (T : Type) :
  Sized.AssociatedTypes T
  where

instance Impl_2 (T : Type) : Sized T where

@[reducible] instance Impl_3.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_3_i0 : core_models.clone.Clone T ] :
  Copy.AssociatedTypes T
  where

instance Impl_3
  (T : Type)
  [trait_constr_Impl_3_associated_type_i0 :
    core_models.clone.Clone.AssociatedTypes
    T]
  [trait_constr_Impl_3_i0 : core_models.clone.Clone T ] :
  Copy T
  where

structure PhantomData (T : Type) where

end core_models.marker


namespace core_models.mem

opaque forget (T : Type) (t : T) : RustM rust_primitives.hax.Tuple0

opaque forget_unsized (T : Type) (t : T) : RustM rust_primitives.hax.Tuple0

opaque size_of (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

opaque size_of_val (T : Type) (val : T) : RustM usize

opaque min_align_of (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

opaque min_align_of_val (T : Type) (val : T) : RustM usize

opaque align_of (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

opaque align_of_val (T : Type) (val : T) : RustM usize

opaque align_of_val_raw (T : Type) (val : T) : RustM usize

opaque needs_drop (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM Bool

opaque uninitialized (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T

opaque swap (T : Type) (x : T) (y : T) : RustM (rust_primitives.hax.Tuple2 T T)

opaque replace (T : Type) (dest : T) (src : T) :
    RustM (rust_primitives.hax.Tuple2 T T)

opaque drop (T : Type) (_x : T) : RustM rust_primitives.hax.Tuple0

@[spec]
def copy
    (T : Type)
    [trait_constr_copy_associated_type_i0 : core.marker.Copy.AssociatedTypes T]
    [trait_constr_copy_i0 : core.marker.Copy T ]
    (x : T) :
    RustM T := do
  (pure x)

opaque take (T : Type) (x : T) : RustM (rust_primitives.hax.Tuple2 T T)

opaque transmute_copy (Src : Type) (Dst : Type) (src : Src) : RustM Dst

opaque variant_count (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM usize

opaque zeroed (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T

opaque transmute (Src : Type) (Dst : Type) (src : Src) : RustM Dst

end core_models.mem


namespace core_models.mem.manually_drop

structure ManuallyDrop (T : Type) where
  value : T

end core_models.mem.manually_drop


namespace core_models.num.error

structure TryFromIntError where
  _0 : rust_primitives.hax.Tuple0

structure IntErrorKind where
  -- no fields

structure ParseIntError where
  kind : IntErrorKind

end core_models.num.error


namespace core_models.num

@[spec]
def Impl_6.wrapping_add (x : u8) (y : u8) : RustM u8 := do
  (rust_primitives.arithmetic.wrapping_add_u8 x y)

@[spec]
def Impl_6.wrapping_sub (x : u8) (y : u8) : RustM u8 := do
  (rust_primitives.arithmetic.wrapping_sub_u8 x y)

@[spec]
def Impl_6.wrapping_mul (x : u8) (y : u8) : RustM u8 := do
  (rust_primitives.arithmetic.wrapping_mul_u8 x y)

@[spec]
def Impl_6.pow (x : u8) (exp : u32) : RustM u8 := do
  (rust_primitives.arithmetic.pow_u8 x exp)

opaque Impl_6.leading_zeros (x : u8) : RustM u32

opaque Impl_6.ilog2 (x : u8) : RustM u32

@[spec]
def Impl_7.wrapping_add (x : u16) (y : u16) : RustM u16 := do
  (rust_primitives.arithmetic.wrapping_add_u16 x y)

@[spec]
def Impl_7.wrapping_sub (x : u16) (y : u16) : RustM u16 := do
  (rust_primitives.arithmetic.wrapping_sub_u16 x y)

@[spec]
def Impl_7.wrapping_mul (x : u16) (y : u16) : RustM u16 := do
  (rust_primitives.arithmetic.wrapping_mul_u16 x y)

@[spec]
def Impl_7.pow (x : u16) (exp : u32) : RustM u16 := do
  (rust_primitives.arithmetic.pow_u16 x exp)

opaque Impl_7.leading_zeros (x : u16) : RustM u32

opaque Impl_7.ilog2 (x : u16) : RustM u32

@[spec]
def Impl_8.wrapping_add (x : u32) (y : u32) : RustM u32 := do
  (rust_primitives.arithmetic.wrapping_add_u32 x y)

@[spec]
def Impl_8.wrapping_sub (x : u32) (y : u32) : RustM u32 := do
  (rust_primitives.arithmetic.wrapping_sub_u32 x y)

@[spec]
def Impl_8.wrapping_mul (x : u32) (y : u32) : RustM u32 := do
  (rust_primitives.arithmetic.wrapping_mul_u32 x y)

@[spec]
def Impl_8.pow (x : u32) (exp : u32) : RustM u32 := do
  (rust_primitives.arithmetic.pow_u32 x exp)

opaque Impl_8.leading_zeros (x : u32) : RustM u32

opaque Impl_8.ilog2 (x : u32) : RustM u32

@[spec]
def Impl_9.wrapping_add (x : u64) (y : u64) : RustM u64 := do
  (rust_primitives.arithmetic.wrapping_add_u64 x y)

@[spec]
def Impl_9.wrapping_sub (x : u64) (y : u64) : RustM u64 := do
  (rust_primitives.arithmetic.wrapping_sub_u64 x y)

@[spec]
def Impl_9.wrapping_mul (x : u64) (y : u64) : RustM u64 := do
  (rust_primitives.arithmetic.wrapping_mul_u64 x y)

@[spec]
def Impl_9.pow (x : u64) (exp : u32) : RustM u64 := do
  (rust_primitives.arithmetic.pow_u64 x exp)

opaque Impl_9.leading_zeros (x : u64) : RustM u32

opaque Impl_9.ilog2 (x : u64) : RustM u32

@[spec]
def Impl_10.wrapping_add (x : u128) (y : u128) : RustM u128 := do
  (rust_primitives.arithmetic.wrapping_add_u128 x y)

@[spec]
def Impl_10.wrapping_sub (x : u128) (y : u128) : RustM u128 := do
  (rust_primitives.arithmetic.wrapping_sub_u128 x y)

@[spec]
def Impl_10.wrapping_mul (x : u128) (y : u128) : RustM u128 := do
  (rust_primitives.arithmetic.wrapping_mul_u128 x y)

@[spec]
def Impl_10.pow (x : u128) (exp : u32) : RustM u128 := do
  (rust_primitives.arithmetic.pow_u128 x exp)

opaque Impl_10.leading_zeros (x : u128) : RustM u32

opaque Impl_10.ilog2 (x : u128) : RustM u32

@[spec]
def Impl_11.wrapping_add (x : usize) (y : usize) : RustM usize := do
  (rust_primitives.arithmetic.wrapping_add_usize x y)

@[spec]
def Impl_11.wrapping_sub (x : usize) (y : usize) : RustM usize := do
  (rust_primitives.arithmetic.wrapping_sub_usize x y)

@[spec]
def Impl_11.wrapping_mul (x : usize) (y : usize) : RustM usize := do
  (rust_primitives.arithmetic.wrapping_mul_usize x y)

@[spec]
def Impl_11.pow (x : usize) (exp : u32) : RustM usize := do
  (rust_primitives.arithmetic.pow_usize x exp)

opaque Impl_11.leading_zeros (x : usize) : RustM u32

opaque Impl_11.ilog2 (x : usize) : RustM u32

@[spec]
def Impl_12.wrapping_add (x : i8) (y : i8) : RustM i8 := do
  (rust_primitives.arithmetic.wrapping_add_i8 x y)

@[spec]
def Impl_12.wrapping_sub (x : i8) (y : i8) : RustM i8 := do
  (rust_primitives.arithmetic.wrapping_sub_i8 x y)

@[spec]
def Impl_12.wrapping_mul (x : i8) (y : i8) : RustM i8 := do
  (rust_primitives.arithmetic.wrapping_mul_i8 x y)

@[spec]
def Impl_12.pow (x : i8) (exp : u32) : RustM i8 := do
  (rust_primitives.arithmetic.pow_i8 x exp)

opaque Impl_12.leading_zeros (x : i8) : RustM u32

opaque Impl_12.ilog2 (x : i8) : RustM u32

@[spec]
def Impl_13.wrapping_add (x : i16) (y : i16) : RustM i16 := do
  (rust_primitives.arithmetic.wrapping_add_i16 x y)

@[spec]
def Impl_13.wrapping_sub (x : i16) (y : i16) : RustM i16 := do
  (rust_primitives.arithmetic.wrapping_sub_i16 x y)

@[spec]
def Impl_13.wrapping_mul (x : i16) (y : i16) : RustM i16 := do
  (rust_primitives.arithmetic.wrapping_mul_i16 x y)

@[spec]
def Impl_13.pow (x : i16) (exp : u32) : RustM i16 := do
  (rust_primitives.arithmetic.pow_i16 x exp)

opaque Impl_13.leading_zeros (x : i16) : RustM u32

opaque Impl_13.ilog2 (x : i16) : RustM u32

@[spec]
def Impl_14.wrapping_add (x : i32) (y : i32) : RustM i32 := do
  (rust_primitives.arithmetic.wrapping_add_i32 x y)

@[spec]
def Impl_14.wrapping_sub (x : i32) (y : i32) : RustM i32 := do
  (rust_primitives.arithmetic.wrapping_sub_i32 x y)

@[spec]
def Impl_14.wrapping_mul (x : i32) (y : i32) : RustM i32 := do
  (rust_primitives.arithmetic.wrapping_mul_i32 x y)

@[spec]
def Impl_14.pow (x : i32) (exp : u32) : RustM i32 := do
  (rust_primitives.arithmetic.pow_i32 x exp)

opaque Impl_14.leading_zeros (x : i32) : RustM u32

opaque Impl_14.ilog2 (x : i32) : RustM u32

@[spec]
def Impl_15.wrapping_add (x : i64) (y : i64) : RustM i64 := do
  (rust_primitives.arithmetic.wrapping_add_i64 x y)

@[spec]
def Impl_15.wrapping_sub (x : i64) (y : i64) : RustM i64 := do
  (rust_primitives.arithmetic.wrapping_sub_i64 x y)

@[spec]
def Impl_15.wrapping_mul (x : i64) (y : i64) : RustM i64 := do
  (rust_primitives.arithmetic.wrapping_mul_i64 x y)

@[spec]
def Impl_15.pow (x : i64) (exp : u32) : RustM i64 := do
  (rust_primitives.arithmetic.pow_i64 x exp)

opaque Impl_15.leading_zeros (x : i64) : RustM u32

opaque Impl_15.ilog2 (x : i64) : RustM u32

@[spec]
def Impl_16.wrapping_add (x : i128) (y : i128) : RustM i128 := do
  (rust_primitives.arithmetic.wrapping_add_i128 x y)

@[spec]
def Impl_16.wrapping_sub (x : i128) (y : i128) : RustM i128 := do
  (rust_primitives.arithmetic.wrapping_sub_i128 x y)

@[spec]
def Impl_16.wrapping_mul (x : i128) (y : i128) : RustM i128 := do
  (rust_primitives.arithmetic.wrapping_mul_i128 x y)

@[spec]
def Impl_16.pow (x : i128) (exp : u32) : RustM i128 := do
  (rust_primitives.arithmetic.pow_i128 x exp)

opaque Impl_16.leading_zeros (x : i128) : RustM u32

opaque Impl_16.ilog2 (x : i128) : RustM u32

@[spec]
def Impl_17.wrapping_add (x : isize) (y : isize) : RustM isize := do
  (rust_primitives.arithmetic.wrapping_add_isize x y)

@[spec]
def Impl_17.wrapping_sub (x : isize) (y : isize) : RustM isize := do
  (rust_primitives.arithmetic.wrapping_sub_isize x y)

@[spec]
def Impl_17.wrapping_mul (x : isize) (y : isize) : RustM isize := do
  (rust_primitives.arithmetic.wrapping_mul_isize x y)

@[spec]
def Impl_17.pow (x : isize) (exp : u32) : RustM isize := do
  (rust_primitives.arithmetic.pow_isize x exp)

opaque Impl_17.leading_zeros (x : isize) : RustM u32

opaque Impl_17.ilog2 (x : isize) : RustM u32

@[reducible] instance Impl_18.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u8
  where

instance Impl_18 : core_models.default.Default u8 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u8))

@[reducible] instance Impl_19.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u16
  where

instance Impl_19 : core_models.default.Default u16 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u16))

@[reducible] instance Impl_20.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u32
  where

instance Impl_20 : core_models.default.Default u32 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u32))

@[reducible] instance Impl_21.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u64
  where

instance Impl_21 : core_models.default.Default u64 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u64))

@[reducible] instance Impl_22.AssociatedTypes :
  core_models.default.Default.AssociatedTypes u128
  where

instance Impl_22 : core_models.default.Default u128 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : u128))

@[reducible] instance Impl_23.AssociatedTypes :
  core_models.default.Default.AssociatedTypes usize
  where

instance Impl_23 : core_models.default.Default usize where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : usize))

@[reducible] instance Impl_24.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i8
  where

instance Impl_24 : core_models.default.Default i8 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i8))

@[reducible] instance Impl_25.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i16
  where

instance Impl_25 : core_models.default.Default i16 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i16))

@[reducible] instance Impl_26.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i32
  where

instance Impl_26 : core_models.default.Default i32 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i32))

@[reducible] instance Impl_27.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i64
  where

instance Impl_27 : core_models.default.Default i64 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i64))

@[reducible] instance Impl_28.AssociatedTypes :
  core_models.default.Default.AssociatedTypes i128
  where

instance Impl_28 : core_models.default.Default i128 where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : i128))

@[reducible] instance Impl_29.AssociatedTypes :
  core_models.default.Default.AssociatedTypes isize
  where

instance Impl_29 : core_models.default.Default isize where
  default := fun (_ : rust_primitives.hax.Tuple0) => do (pure (0 : isize))

end core_models.num


namespace core_models.ops.arith

class AddAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class AddAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (AddAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  add_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class SubAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class SubAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (SubAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  sub_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class MulAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class MulAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (MulAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  mul_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class DivAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class DivAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (DivAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  div_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

class RemAssign.AssociatedTypes (Self : Type) (Rhs : Type) where

class RemAssign (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (RemAssign.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  rem_assign (Self) (Rhs) : (Self -> Rhs -> RustM Self)

end core_models.ops.arith


namespace core_models.ops.control_flow

inductive ControlFlow (B : Type) (C : Type) : Type
| Continue : C -> ControlFlow (B : Type) (C : Type)
| Break : B -> ControlFlow (B : Type) (C : Type)

end core_models.ops.control_flow


namespace core_models.ops.try_trait

class FromResidual.AssociatedTypes (Self : Type) (R : Type) where

class FromResidual (Self : Type) (R : Type)
  [associatedTypes : outParam (FromResidual.AssociatedTypes (Self : Type) (R :
      Type))]
  where
  from_residual (Self) (R) : (R -> RustM Self)

end core_models.ops.try_trait


namespace core_models.ops.drop

class Drop.AssociatedTypes (Self : Type) where

class Drop (Self : Type)
  [associatedTypes : outParam (Drop.AssociatedTypes (Self : Type))]
  where
  drop (Self) : (Self -> RustM Self)

end core_models.ops.drop


namespace core_models.ops.range

structure RangeTo (T : Type) where
  _end : T

structure RangeFrom (T : Type) where
  start : T

structure Range (T : Type) where
  start : T
  _end : T

structure RangeFull where
  -- no fields

end core_models.ops.range


namespace core_models.option

inductive Option (T : Type) : Type
| Some : T -> Option (T : Type)
| None : Option (T : Type)

end core_models.option


namespace core_models.cmp

class PartialOrd.AssociatedTypes (Self : Type) (Rhs : Type) where
  [trait_constr_PartialOrd_i0 : PartialEq.AssociatedTypes Self Rhs]

attribute [instance] PartialOrd.AssociatedTypes.trait_constr_PartialOrd_i0

class PartialOrd (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialOrd.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  [trait_constr_PartialOrd_i0 : PartialEq Self Rhs]
  partial_cmp (Self) (Rhs) :
    (Self -> Rhs -> RustM (core_models.option.Option Ordering))

attribute [instance] PartialOrd.trait_constr_PartialOrd_i0

class PartialOrdDefaults.AssociatedTypes (Self : Type) (Rhs : Type) where

class PartialOrdDefaults (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (PartialOrdDefaults.AssociatedTypes (Self : Type)
      (Rhs : Type))]
  where
  lt (Self) (Rhs)
    [trait_constr_lt_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_lt_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)
  le (Self) (Rhs)
    [trait_constr_le_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_le_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)
  gt (Self) (Rhs)
    [trait_constr_gt_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_gt_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)
  ge (Self) (Rhs)
    [trait_constr_ge_associated_type_i1 : PartialOrd.AssociatedTypes Self Rhs]
    [trait_constr_ge_i1 : PartialOrd Self Rhs ] :
    (Self -> Rhs -> RustM Bool)

@[reducible] instance Impl_1.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_1_i0 : PartialOrd T T ] :
  PartialOrdDefaults.AssociatedTypes T T
  where

instance Impl_1
  (T : Type)
  [trait_constr_Impl_1_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_1_i0 : PartialOrd T T ] :
  PartialOrdDefaults T T
  where
  lt :=
    fun
      [trait_constr_lt_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_lt_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Less )) => do (pure true)
      | _ => do (pure false)
  le :=
    fun
      [trait_constr_le_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_le_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Less )) |
        (core_models.option.Option.Some  (Ordering.Equal )) => do
        (pure true)
      | _ => do (pure false)
  gt :=
    fun
      [trait_constr_gt_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_gt_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Greater )) => do (pure true)
      | _ => do (pure false)
  ge :=
    fun
      [trait_constr_ge_associated_type_i1 : PartialOrd.AssociatedTypes T T]
      [trait_constr_ge_i1 : PartialOrd T T ] (self : T) (y : T) => do
    match (← (PartialOrd.partial_cmp T T self y)) with
      | (core_models.option.Option.Some  (Ordering.Greater )) |
        (core_models.option.Option.Some  (Ordering.Equal )) => do
        (pure true)
      | _ => do (pure false)

class Ord.AssociatedTypes (Self : Type) where
  [trait_constr_Ord_i0 : Eq.AssociatedTypes Self]
  [trait_constr_Ord_i1 : PartialOrd.AssociatedTypes Self Self]

attribute [instance] Ord.AssociatedTypes.trait_constr_Ord_i0

attribute [instance] Ord.AssociatedTypes.trait_constr_Ord_i1

class Ord (Self : Type)
  [associatedTypes : outParam (Ord.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Ord_i0 : Eq Self]
  [trait_constr_Ord_i1 : PartialOrd Self Self]
  cmp (Self) : (Self -> Self -> RustM Ordering)

attribute [instance] Ord.trait_constr_Ord_i0

attribute [instance] Ord.trait_constr_Ord_i1

@[spec]
def max
    (T : Type)
    [trait_constr_max_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_max_i0 : Ord T ]
    (v1 : T)
    (v2 : T) :
    RustM T := do
  match (← (Ord.cmp T v1 v2)) with
    | (Ordering.Greater ) => do (pure v1)
    | _ => do (pure v2)

@[spec]
def min
    (T : Type)
    [trait_constr_min_associated_type_i0 : Ord.AssociatedTypes T]
    [trait_constr_min_i0 : Ord T ]
    (v1 : T)
    (v2 : T) :
    RustM T := do
  match (← (Ord.cmp T v1 v2)) with
    | (Ordering.Greater ) => do (pure v2)
    | _ => do (pure v1)

@[reducible] instance Impl_2.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_2_i0 : PartialOrd T T ] :
  PartialOrd.AssociatedTypes (Reverse T) (Reverse T)
  where

instance Impl_2
  (T : Type)
  [trait_constr_Impl_2_associated_type_i0 : PartialOrd.AssociatedTypes T T]
  [trait_constr_Impl_2_i0 : PartialOrd T T ] :
  PartialOrd (Reverse T) (Reverse T)
  where
  partial_cmp := fun (self : (Reverse T)) (other : (Reverse T)) => do
    (PartialOrd.partial_cmp T T (Reverse._0 other) (Reverse._0 self))

@[reducible] instance Impl_5.AssociatedTypes
  (T : Type)
  [trait_constr_Impl_5_associated_type_i0 : Ord.AssociatedTypes T]
  [trait_constr_Impl_5_i0 : Ord T ] :
  Ord.AssociatedTypes (Reverse T)
  where

instance Impl_5
  (T : Type)
  [trait_constr_Impl_5_associated_type_i0 : Ord.AssociatedTypes T]
  [trait_constr_Impl_5_i0 : Ord T ] :
  Ord (Reverse T)
  where
  cmp := fun (self : (Reverse T)) (other : (Reverse T)) => do
    (Ord.cmp T (Reverse._0 other) (Reverse._0 self))

@[reducible] instance Impl_30.AssociatedTypes :
  PartialOrd.AssociatedTypes u8 u8
  where

instance Impl_30 : PartialOrd u8 u8 where
  partial_cmp := fun (self : u8) (other : u8) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_31.AssociatedTypes : Ord.AssociatedTypes u8 where

instance Impl_31 : Ord u8 where
  cmp := fun (self : u8) (other : u8) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_32.AssociatedTypes :
  PartialOrd.AssociatedTypes i8 i8
  where

instance Impl_32 : PartialOrd i8 i8 where
  partial_cmp := fun (self : i8) (other : i8) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_33.AssociatedTypes : Ord.AssociatedTypes i8 where

instance Impl_33 : Ord i8 where
  cmp := fun (self : i8) (other : i8) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_34.AssociatedTypes :
  PartialOrd.AssociatedTypes u16 u16
  where

instance Impl_34 : PartialOrd u16 u16 where
  partial_cmp := fun (self : u16) (other : u16) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_35.AssociatedTypes : Ord.AssociatedTypes u16 where

instance Impl_35 : Ord u16 where
  cmp := fun (self : u16) (other : u16) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_36.AssociatedTypes :
  PartialOrd.AssociatedTypes i16 i16
  where

instance Impl_36 : PartialOrd i16 i16 where
  partial_cmp := fun (self : i16) (other : i16) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_37.AssociatedTypes : Ord.AssociatedTypes i16 where

instance Impl_37 : Ord i16 where
  cmp := fun (self : i16) (other : i16) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_38.AssociatedTypes :
  PartialOrd.AssociatedTypes u32 u32
  where

instance Impl_38 : PartialOrd u32 u32 where
  partial_cmp := fun (self : u32) (other : u32) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_39.AssociatedTypes : Ord.AssociatedTypes u32 where

instance Impl_39 : Ord u32 where
  cmp := fun (self : u32) (other : u32) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_40.AssociatedTypes :
  PartialOrd.AssociatedTypes i32 i32
  where

instance Impl_40 : PartialOrd i32 i32 where
  partial_cmp := fun (self : i32) (other : i32) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_41.AssociatedTypes : Ord.AssociatedTypes i32 where

instance Impl_41 : Ord i32 where
  cmp := fun (self : i32) (other : i32) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_42.AssociatedTypes :
  PartialOrd.AssociatedTypes u64 u64
  where

instance Impl_42 : PartialOrd u64 u64 where
  partial_cmp := fun (self : u64) (other : u64) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_43.AssociatedTypes : Ord.AssociatedTypes u64 where

instance Impl_43 : Ord u64 where
  cmp := fun (self : u64) (other : u64) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_44.AssociatedTypes :
  PartialOrd.AssociatedTypes i64 i64
  where

instance Impl_44 : PartialOrd i64 i64 where
  partial_cmp := fun (self : i64) (other : i64) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_45.AssociatedTypes : Ord.AssociatedTypes i64 where

instance Impl_45 : Ord i64 where
  cmp := fun (self : i64) (other : i64) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_46.AssociatedTypes :
  PartialOrd.AssociatedTypes u128 u128
  where

instance Impl_46 : PartialOrd u128 u128 where
  partial_cmp := fun (self : u128) (other : u128) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_47.AssociatedTypes : Ord.AssociatedTypes u128 where

instance Impl_47 : Ord u128 where
  cmp := fun (self : u128) (other : u128) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_48.AssociatedTypes :
  PartialOrd.AssociatedTypes i128 i128
  where

instance Impl_48 : PartialOrd i128 i128 where
  partial_cmp := fun (self : i128) (other : i128) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_49.AssociatedTypes : Ord.AssociatedTypes i128 where

instance Impl_49 : Ord i128 where
  cmp := fun (self : i128) (other : i128) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_50.AssociatedTypes :
  PartialOrd.AssociatedTypes usize usize
  where

instance Impl_50 : PartialOrd usize usize where
  partial_cmp := fun (self : usize) (other : usize) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_51.AssociatedTypes : Ord.AssociatedTypes usize where

instance Impl_51 : Ord usize where
  cmp := fun (self : usize) (other : usize) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

@[reducible] instance Impl_52.AssociatedTypes :
  PartialOrd.AssociatedTypes isize isize
  where

instance Impl_52 : PartialOrd isize isize where
  partial_cmp := fun (self : isize) (other : isize) => do
    if (← (self <? other)) then do
      (pure (core_models.option.Option.Some Ordering.Less))
    else do
      if (← (self >? other)) then do
        (pure (core_models.option.Option.Some Ordering.Greater))
      else do
        (pure (core_models.option.Option.Some Ordering.Equal))

@[reducible] instance Impl_53.AssociatedTypes : Ord.AssociatedTypes isize where

instance Impl_53 : Ord isize where
  cmp := fun (self : isize) (other : isize) => do
    if (← (self <? other)) then do
      (pure Ordering.Less)
    else do
      if (← (self >? other)) then do
        (pure Ordering.Greater)
      else do
        (pure Ordering.Equal)

end core_models.cmp


namespace core_models.iter.adapters.flat_map

structure FlatMap (I : Type) (U : Type) (F : Type) where
  it : I
  f : F
  current : (core_models.option.Option U)

end core_models.iter.adapters.flat_map


namespace core_models.option

@[spec]
def Impl.as_ref (T : Type) (self : (Option T)) : RustM (Option T) := do
  match self with
    | (Option.Some  x) => do (pure (Option.Some x))
    | (Option.None ) => do (pure Option.None)

@[spec]
def Impl.unwrap_or (T : Type) (self : (Option T)) (default : T) : RustM T := do
  match self with
    | (Option.Some  x) => do (pure x)
    | (Option.None ) => do (pure default)

@[spec]
def Impl.unwrap_or_default
    (T : Type)
    [trait_constr_unwrap_or_default_associated_type_i0 :
      core_models.default.Default.AssociatedTypes
      T]
    [trait_constr_unwrap_or_default_i0 : core_models.default.Default T ]
    (self : (Option T)) :
    RustM T := do
  match self with
    | (Option.Some  x) => do (pure x)
    | (Option.None ) => do
      (core_models.default.Default.default T rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl.take (T : Type) (self : (Option T)) :
    RustM (rust_primitives.hax.Tuple2 (Option T) (Option T)) := do
  (pure (rust_primitives.hax.Tuple2.mk Option.None self))

def Impl.is_some (T : Type) (self : (Option T)) : RustM Bool := do
  match self with | (Option.Some  _) => do (pure true) | _ => do (pure false)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl.is_some.spec (T : Type) (self : (Option T)) :
    Spec
      (requires := do pure True)
      (ensures := fun
          res => do
          (hax_lib.prop.constructors.implies
            (← (hax_lib.prop.constructors.from_bool res))
            (← (hax_lib.prop.Impl.from_bool true))))
      (Impl.is_some (T : Type) (self : (Option T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.is_some] <;> bv_decide
}

@[spec]
def Impl.is_none (T : Type) (self : (Option T)) : RustM Bool := do
  ((← (Impl.is_some T self)) ==? false)

end core_models.option


namespace core_models.panicking

opaque panic_explicit (_ : rust_primitives.hax.Tuple0) :
    RustM rust_primitives.hax.Never

opaque panic (_msg : String) : RustM rust_primitives.hax.Never

opaque panic_fmt (_fmt : core_models.fmt.Arguments) :
    RustM rust_primitives.hax.Never

end core_models.panicking


namespace core_models.panicking.internal

opaque panic (T : Type) (_ : rust_primitives.hax.Tuple0) : RustM T

end core_models.panicking.internal


namespace core_models.hash

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Hash.AssociatedTypes T
  where

instance Impl (T : Type) : Hash T where
  hash :=
    fun
      (H : Type)
      [trait_constr_hash_associated_type_i0 : Hasher.AssociatedTypes H]
      [trait_constr_hash_i0 : Hasher H ] (self : T) (h : H) => do
    (core_models.panicking.internal.panic H rust_primitives.hax.Tuple0.mk)

end core_models.hash


namespace core_models.result

inductive Result (T : Type) (E : Type) : Type
| Ok : T -> Result (T : Type) (E : Type)
| Err : E -> Result (T : Type) (E : Type)

end core_models.result


namespace core_models.fmt

abbrev Result :
  Type :=
  (core_models.result.Result rust_primitives.hax.Tuple0 Error)

class Display.AssociatedTypes (Self : Type) where

class Display (Self : Type)
  [associatedTypes : outParam (Display.AssociatedTypes (Self : Type))]
  where
  fmt (Self) :
    (Self ->
    Formatter ->
    RustM (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error)))

class Debug.AssociatedTypes (Self : Type) where

class Debug (Self : Type)
  [associatedTypes : outParam (Debug.AssociatedTypes (Self : Type))]
  where
  dbg_fmt (Self) :
    (Self ->
    Formatter ->
    RustM (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error)))

end core_models.fmt


namespace core_models.error

class Error.AssociatedTypes (Self : Type) where
  [trait_constr_Error_i0 : core_models.fmt.Display.AssociatedTypes Self]
  [trait_constr_Error_i1 : core_models.fmt.Debug.AssociatedTypes Self]

attribute [instance] Error.AssociatedTypes.trait_constr_Error_i0

attribute [instance] Error.AssociatedTypes.trait_constr_Error_i1

class Error (Self : Type)
  [associatedTypes : outParam (Error.AssociatedTypes (Self : Type))]
  where
  [trait_constr_Error_i0 : core_models.fmt.Display Self]
  [trait_constr_Error_i1 : core_models.fmt.Debug Self]

attribute [instance] Error.trait_constr_Error_i0

attribute [instance] Error.trait_constr_Error_i1

end core_models.error


namespace core_models.fmt

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Debug.AssociatedTypes T
  where

instance Impl (T : Type) : Debug T where
  dbg_fmt := fun (self : T) (f : Formatter) => do
    let
      hax_temp_output : (core_models.result.Result
        rust_primitives.hax.Tuple0
        Error) :=
      (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
    (pure (rust_primitives.hax.Tuple2.mk f hax_temp_output))

@[spec]
def Impl_11.write_fmt (f : Formatter) (args : Arguments) :
    RustM
    (rust_primitives.hax.Tuple2
      Formatter
      (core_models.result.Result rust_primitives.hax.Tuple0 Error))
    := do
  let
    hax_temp_output : (core_models.result.Result
      rust_primitives.hax.Tuple0
      Error) :=
    (core_models.result.Result.Ok rust_primitives.hax.Tuple0.mk);
  (pure (rust_primitives.hax.Tuple2.mk f hax_temp_output))

end core_models.fmt


namespace core_models.num

opaque Impl_6.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u8 core_models.num.error.ParseIntError)

opaque Impl_7.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u16 core_models.num.error.ParseIntError)

opaque Impl_8.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u32 core_models.num.error.ParseIntError)

opaque Impl_9.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u64 core_models.num.error.ParseIntError)

opaque Impl_10.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result u128 core_models.num.error.ParseIntError)

opaque Impl_11.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result usize core_models.num.error.ParseIntError)

opaque Impl_12.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i8 core_models.num.error.ParseIntError)

opaque Impl_13.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i16 core_models.num.error.ParseIntError)

opaque Impl_14.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i32 core_models.num.error.ParseIntError)

opaque Impl_15.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i64 core_models.num.error.ParseIntError)

opaque Impl_16.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result i128 core_models.num.error.ParseIntError)

opaque Impl_17.from_str_radix (src : String) (radix : u32) :
    RustM (core_models.result.Result isize core_models.num.error.ParseIntError)

end core_models.num


namespace core_models.option

@[spec]
def Impl.ok_or (T : Type) (E : Type) (self : (Option T)) (err : E) :
    RustM (core_models.result.Result T E) := do
  match self with
    | (Option.Some  v) => do (pure (core_models.result.Result.Ok v))
    | (Option.None ) => do (pure (core_models.result.Result.Err err))

end core_models.option


namespace core_models.result

@[spec]
def Impl.unwrap_or (T : Type) (E : Type) (self : (Result T E)) (default : T) :
    RustM T := do
  match self with
    | (Result.Ok  t) => do (pure t)
    | (Result.Err  _) => do (pure default)

@[spec]
def Impl.is_ok (T : Type) (E : Type) (self : (Result T E)) : RustM Bool := do
  match self with | (Result.Ok  _) => do (pure true) | _ => do (pure false)

@[spec]
def Impl.ok (T : Type) (E : Type) (self : (Result T E)) :
    RustM (core_models.option.Option T) := do
  match self with
    | (Result.Ok  x) => do (pure (core_models.option.Option.Some x))
    | (Result.Err  _) => do (pure core_models.option.Option.None)

end core_models.result


namespace core_models.slice.iter

structure Chunks (T : Type) where
  cs : usize
  elements : (RustSlice T)

@[spec]
def Impl.new (T : Type) (cs : usize) (elements : (RustSlice T)) :
    RustM (Chunks T) := do
  (pure (Chunks.mk (cs := cs) (elements := elements)))

structure ChunksExact (T : Type) where
  cs : usize
  elements : (RustSlice T)

@[spec]
def Impl_1.new (T : Type) (cs : usize) (elements : (RustSlice T)) :
    RustM (ChunksExact T) := do
  (pure (ChunksExact.mk (cs := cs) (elements := elements)))

structure Iter (T : Type) where
  _0 : (rust_primitives.sequence.Seq T)

end core_models.slice.iter


namespace core_models.slice

@[spec]
def Impl.len (T : Type) (s : (RustSlice T)) : RustM usize := do
  (rust_primitives.slice.slice_length T s)

@[spec]
def Impl.chunks (T : Type) (s : (RustSlice T)) (cs : usize) :
    RustM (core_models.slice.iter.Chunks T) := do
  (core_models.slice.iter.Impl.new T cs s)

@[spec]
def Impl.iter (T : Type) (s : (RustSlice T)) :
    RustM (core_models.slice.iter.Iter T) := do
  (pure (core_models.slice.iter.Iter.mk
    (← (rust_primitives.sequence.seq_from_slice T s))))

@[spec]
def Impl.chunks_exact (T : Type) (s : (RustSlice T)) (cs : usize) :
    RustM (core_models.slice.iter.ChunksExact T) := do
  (core_models.slice.iter.Impl_1.new T cs s)

@[spec]
def Impl.is_empty (T : Type) (s : (RustSlice T)) : RustM Bool := do
  ((← (Impl.len T s)) ==? (0 : usize))

opaque Impl.contains (T : Type) (s : (RustSlice T)) (v : T) : RustM Bool

opaque Impl.copy_within
    (T : Type)
    (R : Type)
    [trait_constr_copy_within_associated_type_i0 :
      core.marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_within_i0 : core.marker.Copy T ]
    (s : (RustSlice T))
    (src : R)
    (dest : usize) :
    RustM (RustSlice T)

opaque Impl.binary_search (T : Type) (s : (RustSlice T)) (x : T) :
    RustM (core_models.result.Result usize usize)

def Impl.copy_from_slice
    (T : Type)
    [trait_constr_copy_from_slice_associated_type_i0 :
      core_models.marker.Copy.AssociatedTypes
      T]
    [trait_constr_copy_from_slice_i0 : core_models.marker.Copy T ]
    (s : (RustSlice T))
    (src : (RustSlice T)) :
    RustM (RustSlice T) := do
  let ⟨tmp0, out⟩ ← (rust_primitives.mem.replace (RustSlice T) s src);
  let s : (RustSlice T) := tmp0;
  let _ := out;
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.copy_from_slice.spec
      (T : Type)
      [trait_constr_copy_from_slice_associated_type_i0 :
        core_models.marker.Copy.AssociatedTypes
        T]
      [trait_constr_copy_from_slice_i0 : core_models.marker.Copy T ]
      (s : (RustSlice T))
      (src : (RustSlice T)) :
    Spec
      (requires := do ((← (Impl.len T s)) ==? (← (Impl.len T src))))
      (ensures := fun _ => pure True)
      (Impl.copy_from_slice
        (T : Type)
        (s : (RustSlice T))
        (src : (RustSlice T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.copy_from_slice] <;> bv_decide
}

def Impl.clone_from_slice
    (T : Type)
    [trait_constr_clone_from_slice_associated_type_i0 :
      core_models.clone.Clone.AssociatedTypes
      T]
    [trait_constr_clone_from_slice_i0 : core_models.clone.Clone T ]
    (s : (RustSlice T))
    (src : (RustSlice T)) :
    RustM (RustSlice T) := do
  let ⟨tmp0, out⟩ ← (rust_primitives.mem.replace (RustSlice T) s src);
  let s : (RustSlice T) := tmp0;
  let _ := out;
  (pure s)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def
      Impl.clone_from_slice.spec
      (T : Type)
      [trait_constr_clone_from_slice_associated_type_i0 :
        core_models.clone.Clone.AssociatedTypes
        T]
      [trait_constr_clone_from_slice_i0 : core_models.clone.Clone T ]
      (s : (RustSlice T))
      (src : (RustSlice T)) :
    Spec
      (requires := do ((← (Impl.len T s)) ==? (← (Impl.len T src))))
      (ensures := fun _ => pure True)
      (Impl.clone_from_slice
        (T : Type)
        (s : (RustSlice T))
        (src : (RustSlice T))) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.clone_from_slice] <;> bv_decide
}

def Impl.split_at (T : Type) (s : (RustSlice T)) (mid : usize) :
    RustM (rust_primitives.hax.Tuple2 (RustSlice T) (RustSlice T)) := do
  (rust_primitives.slice.slice_split_at T s mid)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def Impl.split_at.spec (T : Type) (s : (RustSlice T)) (mid : usize) :
    Spec
      (requires := do (mid <=? (← (Impl.len T s))))
      (ensures := fun _ => pure True)
      (Impl.split_at (T : Type) (s : (RustSlice T)) (mid : usize)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by hax_mvcgen [Impl.split_at] <;> bv_decide
}

@[spec]
def Impl.split_at_checked (T : Type) (s : (RustSlice T)) (mid : usize) :
    RustM
    (core_models.option.Option
      (rust_primitives.hax.Tuple2 (RustSlice T) (RustSlice T)))
    := do
  if (← (mid <=? (← (Impl.len T s)))) then do
    (pure (core_models.option.Option.Some (← (Impl.split_at T s mid))))
  else do
    (pure core_models.option.Option.None)

end core_models.slice


namespace core_models.str.error

structure Utf8Error where
  -- no fields

end core_models.str.error


namespace core_models.str.converts

opaque from_utf8 (s : (RustSlice u8)) :
    RustM (core_models.result.Result String core_models.str.error.Utf8Error)

end core_models.str.converts


namespace core_models.str.iter

structure Split (T : Type) where
  _0 : T

end core_models.str.iter


namespace core_models.convert

class TryInto.AssociatedTypes (Self : Type) (T : Type) where
  Error : Type

attribute [reducible] TryInto.AssociatedTypes.Error

abbrev TryInto.Error :=
  TryInto.AssociatedTypes.Error

class TryInto (Self : Type) (T : Type)
  [associatedTypes : outParam (TryInto.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  try_into (Self) (T) :
    (Self -> RustM (core_models.result.Result T associatedTypes.Error))

class TryFrom.AssociatedTypes (Self : Type) (T : Type) where
  Error : Type

attribute [reducible] TryFrom.AssociatedTypes.Error

abbrev TryFrom.Error :=
  TryFrom.AssociatedTypes.Error

class TryFrom (Self : Type) (T : Type)
  [associatedTypes : outParam (TryFrom.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  try_from (Self) (T) :
    (T -> RustM (core_models.result.Result Self associatedTypes.Error))

end core_models.convert


namespace core_models.iter.traits.iterator

class Iterator.AssociatedTypes (Self : Type) where
  Item : Type

attribute [reducible] Iterator.AssociatedTypes.Item

abbrev Iterator.Item :=
  Iterator.AssociatedTypes.Item

class Iterator (Self : Type)
  [associatedTypes : outParam (Iterator.AssociatedTypes (Self : Type))]
  where
  next (Self) :
    (Self ->
    RustM (rust_primitives.hax.Tuple2
      Self
      (core_models.option.Option associatedTypes.Item)))

end core_models.iter.traits.iterator


namespace core_models.iter.traits.collect

class IntoIterator.AssociatedTypes (Self : Type) where
  IntoIter : Type

attribute [reducible] IntoIterator.AssociatedTypes.IntoIter

abbrev IntoIterator.IntoIter :=
  IntoIterator.AssociatedTypes.IntoIter

class IntoIterator (Self : Type)
  [associatedTypes : outParam (IntoIterator.AssociatedTypes (Self : Type))]
  where
  into_iter (Self) : (Self -> RustM associatedTypes.IntoIter)

end core_models.iter.traits.collect


namespace core_models.ops.arith

class Add.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Add.AssociatedTypes.Output

abbrev Add.Output :=
  Add.AssociatedTypes.Output

class Add (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Add.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  add (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Sub.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Sub.AssociatedTypes.Output

abbrev Sub.Output :=
  Sub.AssociatedTypes.Output

class Sub (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Sub.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  sub (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Mul.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Mul.AssociatedTypes.Output

abbrev Mul.Output :=
  Mul.AssociatedTypes.Output

class Mul (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Mul.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  mul (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Div.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Div.AssociatedTypes.Output

abbrev Div.Output :=
  Div.AssociatedTypes.Output

class Div (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Div.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  div (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Neg.AssociatedTypes (Self : Type) where
  Output : Type

attribute [reducible] Neg.AssociatedTypes.Output

abbrev Neg.Output :=
  Neg.AssociatedTypes.Output

class Neg (Self : Type)
  [associatedTypes : outParam (Neg.AssociatedTypes (Self : Type))]
  where
  neg (Self) : (Self -> RustM associatedTypes.Output)

class Rem.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Rem.AssociatedTypes.Output

abbrev Rem.Output :=
  Rem.AssociatedTypes.Output

class Rem (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Rem.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  rem (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

end core_models.ops.arith


namespace core_models.ops.bit

class Shr.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Shr.AssociatedTypes.Output

abbrev Shr.Output :=
  Shr.AssociatedTypes.Output

class Shr (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Shr.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  shr (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class Shl.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] Shl.AssociatedTypes.Output

abbrev Shl.Output :=
  Shl.AssociatedTypes.Output

class Shl (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (Shl.AssociatedTypes (Self : Type) (Rhs : Type))]
  where
  shl (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class BitXor.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] BitXor.AssociatedTypes.Output

abbrev BitXor.Output :=
  BitXor.AssociatedTypes.Output

class BitXor (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitXor.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitxor (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

class BitAnd.AssociatedTypes (Self : Type) (Rhs : Type) where
  Output : Type

attribute [reducible] BitAnd.AssociatedTypes.Output

abbrev BitAnd.Output :=
  BitAnd.AssociatedTypes.Output

class BitAnd (Self : Type) (Rhs : Type)
  [associatedTypes : outParam (BitAnd.AssociatedTypes (Self : Type) (Rhs :
      Type))]
  where
  bitand (Self) (Rhs) : (Self -> Rhs -> RustM associatedTypes.Output)

end core_models.ops.bit


namespace core_models.ops.index

class Index.AssociatedTypes (Self : Type) (Idx : Type) where
  Output : Type

attribute [reducible] Index.AssociatedTypes.Output

abbrev Index.Output :=
  Index.AssociatedTypes.Output

class Index (Self : Type) (Idx : Type)
  [associatedTypes : outParam (Index.AssociatedTypes (Self : Type) (Idx :
      Type))]
  where
  index (Self) (Idx) : (Self -> Idx -> RustM associatedTypes.Output)

end core_models.ops.index


namespace core_models.ops.function

class FnOnce.AssociatedTypes (Self : Type) (Args : Type) where
  Output : Type

attribute [reducible] FnOnce.AssociatedTypes.Output

abbrev FnOnce.Output :=
  FnOnce.AssociatedTypes.Output

class FnOnce (Self : Type) (Args : Type)
  [associatedTypes : outParam (FnOnce.AssociatedTypes (Self : Type) (Args :
      Type))]
  where
  call_once (Self) (Args) : (Self -> Args -> RustM associatedTypes.Output)

end core_models.ops.function


namespace core_models.ops.try_trait

class Try.AssociatedTypes (Self : Type) where
  Output : Type
  Residual : Type

attribute [reducible] Try.AssociatedTypes.Output

attribute [reducible] Try.AssociatedTypes.Residual

abbrev Try.Output :=
  Try.AssociatedTypes.Output

abbrev Try.Residual :=
  Try.AssociatedTypes.Residual

class Try (Self : Type)
  [associatedTypes : outParam (Try.AssociatedTypes (Self : Type))]
  where
  from_output (Self) : (associatedTypes.Output -> RustM Self)
  branch (Self) :
    (Self ->
    RustM (core_models.ops.control_flow.ControlFlow
      associatedTypes.Residual
      associatedTypes.Output))

end core_models.ops.try_trait


namespace core_models.ops.deref

class Deref.AssociatedTypes (Self : Type) where
  Target : Type

attribute [reducible] Deref.AssociatedTypes.Target

abbrev Deref.Target :=
  Deref.AssociatedTypes.Target

class Deref (Self : Type)
  [associatedTypes : outParam (Deref.AssociatedTypes (Self : Type))]
  where
  deref (Self) : (Self -> RustM associatedTypes.Target)

end core_models.ops.deref


namespace core_models.slice

class SliceIndex.AssociatedTypes (Self : Type) (T : Type) where
  Output : Type

attribute [reducible] SliceIndex.AssociatedTypes.Output

abbrev SliceIndex.Output :=
  SliceIndex.AssociatedTypes.Output

class SliceIndex (Self : Type) (T : Type)
  [associatedTypes : outParam (SliceIndex.AssociatedTypes (Self : Type) (T :
      Type))]
  where
  get (Self) (T) :
    (Self -> T -> RustM (core_models.option.Option associatedTypes.Output))

end core_models.slice


namespace core_models.str.traits

class FromStr.AssociatedTypes (Self : Type) where
  Err : Type

attribute [reducible] FromStr.AssociatedTypes.Err

abbrev FromStr.Err :=
  FromStr.AssociatedTypes.Err

class FromStr (Self : Type)
  [associatedTypes : outParam (FromStr.AssociatedTypes (Self : Type))]
  where
  from_str (Self) :
    (String -> RustM (core_models.result.Result Self associatedTypes.Err))

end core_models.str.traits


namespace core_models.array

@[spec]
def Impl_23.map
    (T : Type)
    (N : usize)
    (F : Type)
    (U : Type)
    [trait_constr_map_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (s : (RustArray T N))
    (f : (T -> RustM U)) :
    RustM (RustArray U N) := do
  (rust_primitives.slice.array_map T U (N) (T -> RustM U) s f)

@[spec]
def from_fn
    (T : Type)
    (N : usize)
    (F : Type)
    [trait_constr_from_fn_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      usize]
    [trait_constr_from_fn_i0 : core_models.ops.function.FnOnce
      F
      usize
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F usize
        by infer_instance
        with Output := T})]
    (f : (usize -> RustM T)) :
    RustM (RustArray T N) := do
  (rust_primitives.slice.array_from_fn T (N) (usize -> RustM T) f)

end core_models.array


namespace core_models.convert

@[reducible] instance Impl_1.AssociatedTypes
  (T : Type)
  (U : Type)
  [trait_constr_Impl_1_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_1_i0 : From U T ] :
  TryFrom.AssociatedTypes U T
  where
  Error := Infallible

instance Impl_1
  (T : Type)
  (U : Type)
  [trait_constr_Impl_1_associated_type_i0 : From.AssociatedTypes U T]
  [trait_constr_Impl_1_i0 : From U T ] :
  TryFrom U T
  where
  try_from := fun (x : T) => do
    (pure (core_models.result.Result.Ok (← (From._from U T x))))

@[reducible] instance Impl_2.AssociatedTypes
  (T : Type)
  (U : Type)
  [trait_constr_Impl_2_associated_type_i0 : TryFrom.AssociatedTypes U T]
  [trait_constr_Impl_2_i0 : TryFrom U T ] :
  TryInto.AssociatedTypes T U
  where
  Error := (TryFrom.Error U T)

instance Impl_2
  (T : Type)
  (U : Type)
  [trait_constr_Impl_2_associated_type_i0 : TryFrom.AssociatedTypes U T]
  [trait_constr_Impl_2_i0 : TryFrom U T ] :
  TryInto T U
  where
  try_into := fun (self : T) => do (TryFrom.try_from U T self)

end core_models.convert


namespace core_models.iter.traits.iterator

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_1_i0 : Iterator I ] :
  core_models.iter.traits.collect.IntoIterator.AssociatedTypes I
  where
  IntoIter := I

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_1_i0 : Iterator I ] :
  core_models.iter.traits.collect.IntoIterator I
  where
  into_iter := fun (self : I) => do (pure self)

end core_models.iter.traits.iterator


namespace core_models.iter.traits.collect

class FromIterator.AssociatedTypes (Self : Type) (A : Type) where

class FromIterator (Self : Type) (A : Type)
  [associatedTypes : outParam (FromIterator.AssociatedTypes (Self : Type) (A :
      Type))]
  where
  from_iter (Self) (A)
    (T : Type)
    [trait_constr_from_iter_associated_type_i1 : IntoIterator.AssociatedTypes T]
    [trait_constr_from_iter_i1 : IntoIterator T ] :
    (T -> RustM Self)

end core_models.iter.traits.collect


namespace core_models.iter.adapters.enumerate

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Enumerate I)
  where
  Item := (rust_primitives.hax.Tuple2
    usize
    (core_models.iter.traits.iterator.Iterator.Item I))

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (Enumerate I)
  where
  next := fun (self : (Enumerate I)) => do
    let ⟨tmp0, out⟩ ←
      (core_models.iter.traits.iterator.Iterator.next I (Enumerate.iter self));
    let self : (Enumerate I) := {self with iter := tmp0};
    let ⟨self, hax_temp_output⟩ ←
      match out with
        | (core_models.option.Option.Some  a) => do
          let i : usize := (Enumerate.count self);
          let _ ←
            (hax_lib.assume
              (← (hax_lib.prop.constructors.from_bool
                (← ((Enumerate.count self) <? core.num.Impl_11.MAX)))));
          let self : (Enumerate I) :=
            {self with count := (← ((Enumerate.count self) +? (1 : usize)))};
          (pure (rust_primitives.hax.Tuple2.mk
            self
            (core_models.option.Option.Some
              (rust_primitives.hax.Tuple2.mk i a))))
        | (core_models.option.Option.None ) => do
          (pure (rust_primitives.hax.Tuple2.mk
            self
            core_models.option.Option.None));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end core_models.iter.adapters.enumerate


namespace core_models.iter.adapters.step_by

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (StepBy I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (StepBy I) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.step_by


namespace core_models.iter.adapters.map

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  (O : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.ops.function.FnOnce.AssociatedTypes
    F
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : core_models.ops.function.FnOnce
    F
    (core_models.iter.traits.iterator.Iterator.Item I)
    (associatedTypes := {
      show
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (core_models.iter.traits.iterator.Iterator.Item I)
      by infer_instance
      with Output := O})] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Map I F)
  where
  Item := O

instance Impl_1
  (I : Type)
  (O : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.ops.function.FnOnce.AssociatedTypes
    F
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : core_models.ops.function.FnOnce
    F
    (core_models.iter.traits.iterator.Iterator.Item I)
    (associatedTypes := {
      show
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (core_models.iter.traits.iterator.Iterator.Item I)
      by infer_instance
      with Output := O})] :
  core_models.iter.traits.iterator.Iterator (Map I F)
  where
  next := fun (self : (Map I F)) => do
    let ⟨tmp0, out⟩ ←
      (core_models.iter.traits.iterator.Iterator.next I (Map.iter self));
    let self : (Map I F) := {self with iter := tmp0};
    let hax_temp_output : (core_models.option.Option O) ←
      match out with
        | (core_models.option.Option.Some  v) => do
          (pure (core_models.option.Option.Some
            (← (core_models.ops.function.FnOnce.call_once
              F
              (core_models.iter.traits.iterator.Iterator.Item I)
              (Map.f self)
              v))))
        | (core_models.option.Option.None ) => do
          (pure core_models.option.Option.None);
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end core_models.iter.adapters.map


namespace core_models.iter.adapters.take

@[reducible] instance Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Take I)
  where
  Item := (core_models.iter.traits.iterator.Iterator.Item I)

instance Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ] :
  core_models.iter.traits.iterator.Iterator (Take I)
  where
  next := fun (self : (Take I)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← (rust_primitives.hax.machine_int.ne (Take.n self) (0 : usize))) then do
        let self : (Take I) :=
          {self with n := (← ((Take.n self) -? (1 : usize)))};
        let ⟨tmp0, out⟩ ←
          (core_models.iter.traits.iterator.Iterator.next I (Take.iter self));
        let self : (Take I) := {self with iter := tmp0};
        (pure (rust_primitives.hax.Tuple2.mk self out))
      else do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end core_models.iter.adapters.take


namespace core_models.iter.adapters.flat_map

@[spec]
def Impl.new
    (I : Type)
    (U : Type)
    (F : Type)
    [trait_constr_new_associated_type_i0 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I]
    [trait_constr_new_i0 : core_models.iter.traits.iterator.Iterator I ]
    [trait_constr_new_associated_type_i1 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      U]
    [trait_constr_new_i1 : core_models.iter.traits.iterator.Iterator U ]
    [trait_constr_new_associated_type_i2 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      (core_models.iter.traits.iterator.Iterator.Item I)]
    [trait_constr_new_i2 : core_models.ops.function.FnOnce
      F
      (core_models.iter.traits.iterator.Iterator.Item I)
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          (core_models.iter.traits.iterator.Iterator.Item I)
        by infer_instance
        with Output := U})]
    (it : I)
    (f : F) :
    RustM (FlatMap I U F) := do
  (pure (FlatMap.mk
    (it := it)
    (f := f)
    (current := core_models.option.Option.None)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  (U : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    U]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator U ]
  [trait_constr_Impl_1_associated_type_i2 :
    core_models.ops.function.FnOnce.AssociatedTypes
    F
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i2 : core_models.ops.function.FnOnce
    F
    (core_models.iter.traits.iterator.Iterator.Item I)
    (associatedTypes := {
      show
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (core_models.iter.traits.iterator.Iterator.Item I)
      by infer_instance
      with Output := U})] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (FlatMap I U F) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  (U : Type)
  (F : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    U]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator U ]
  [trait_constr_Impl_1_associated_type_i2 :
    core_models.ops.function.FnOnce.AssociatedTypes
    F
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i2 : core_models.ops.function.FnOnce
    F
    (core_models.iter.traits.iterator.Iterator.Item I)
    (associatedTypes := {
      show
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (core_models.iter.traits.iterator.Iterator.Item I)
      by infer_instance
      with Output := U})] :
  core_models.iter.traits.iterator.Iterator (FlatMap I U F) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.flat_map


namespace core_models.iter.adapters.flatten

structure Flatten
  (I : Type)
  [trait_constr_Flatten_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Flatten_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Flatten_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Flatten_i1 : core_models.iter.traits.iterator.Iterator
    (core_models.iter.traits.iterator.Iterator.Item I)
    ]
  where
  it : I
  current : (core_models.option.Option
      (core_models.iter.traits.iterator.Iterator.Item I))

end core_models.iter.adapters.flatten


namespace core_models.iter.traits.iterator

class IteratorMethods.AssociatedTypes (Self : Type) where
  [trait_constr_IteratorMethods_i0 : Iterator.AssociatedTypes Self]

attribute [instance]
  IteratorMethods.AssociatedTypes.trait_constr_IteratorMethods_i0

class IteratorMethods (Self : Type)
  [associatedTypes : outParam (IteratorMethods.AssociatedTypes (Self : Type))]
  where
  [trait_constr_IteratorMethods_i0 : Iterator Self]
  fold (Self)
    (B : Type)
    (F : Type)
    [trait_constr_fold_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      (rust_primitives.hax.Tuple2 B (Iterator.Item Self))]
    [trait_constr_fold_i1 : core_models.ops.function.FnOnce
      F
      (rust_primitives.hax.Tuple2 B (Iterator.Item Self))
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          (rust_primitives.hax.Tuple2 B (Iterator.Item Self))
        by infer_instance
        with Output := B})] :
    (Self -> B -> F -> RustM B)
  enumerate (Self) :
    (Self -> RustM (core_models.iter.adapters.enumerate.Enumerate Self))
  step_by (Self) :
    (Self -> usize -> RustM (core_models.iter.adapters.step_by.StepBy Self))
  map (Self)
    (O : Type)
    (F : Type)
    [trait_constr_map_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      (Iterator.Item Self)]
    [trait_constr_map_i1 : core_models.ops.function.FnOnce
      F
      (Iterator.Item Self)
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          (Iterator.Item Self)
        by infer_instance
        with Output := O})] :
    (Self -> F -> RustM (core_models.iter.adapters.map.Map Self F))
  all (Self)
    (F : Type)
    [trait_constr_all_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      (Iterator.Item Self)]
    [trait_constr_all_i1 : core_models.ops.function.FnOnce
      F
      (Iterator.Item Self)
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          (Iterator.Item Self)
        by infer_instance
        with Output := Bool})] :
    (Self -> F -> RustM Bool)
  take (Self) :
    (Self -> usize -> RustM (core_models.iter.adapters.take.Take Self))
  flat_map (Self)
    (U : Type)
    (F : Type)
    [trait_constr_flat_map_associated_type_i1 : Iterator.AssociatedTypes U]
    [trait_constr_flat_map_i1 : Iterator U ]
    [trait_constr_flat_map_associated_type_i2 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      (Iterator.Item Self)]
    [trait_constr_flat_map_i2 : core_models.ops.function.FnOnce
      F
      (Iterator.Item Self)
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          (Iterator.Item Self)
        by infer_instance
        with Output := U})] :
    (Self -> F -> RustM (core_models.iter.adapters.flat_map.FlatMap Self U F))
  flatten (Self)
    [trait_constr_flatten_associated_type_i1 : Iterator.AssociatedTypes
      (Iterator.Item Self)]
    [trait_constr_flatten_i1 : Iterator (Iterator.Item Self) ] :
    (Self -> RustM (core_models.iter.adapters.flatten.Flatten Self))
  zip (Self)
    (I2 : Type)
    [trait_constr_zip_associated_type_i1 : Iterator.AssociatedTypes I2]
    [trait_constr_zip_i1 : Iterator I2 ] :
    (Self -> I2 -> RustM (core_models.iter.adapters.zip.Zip Self I2))

attribute [instance] IteratorMethods.trait_constr_IteratorMethods_i0

end core_models.iter.traits.iterator


namespace core_models.iter.adapters.flatten

@[spec]
def Impl.new
    (I : Type)
    [trait_constr_new_associated_type_i0 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I]
    [trait_constr_new_i0 : core_models.iter.traits.iterator.Iterator I ]
    [trait_constr_new_associated_type_i1 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      (core_models.iter.traits.iterator.Iterator.Item I)]
    [trait_constr_new_i1 : core_models.iter.traits.iterator.Iterator
      (core_models.iter.traits.iterator.Iterator.Item I)
      ]
    (it : I) :
    RustM (Flatten I) := do
  (pure (Flatten.mk (it := it) (current := core_models.option.Option.None)))

@[instance] opaque Impl_1.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator
    (core_models.iter.traits.iterator.Iterator.Item I)
    ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Flatten I) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    (core_models.iter.traits.iterator.Iterator.Item I)]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator
    (core_models.iter.traits.iterator.Iterator.Item I)
    ] :
  core_models.iter.traits.iterator.Iterator (Flatten I) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.flatten


namespace core_models.iter.adapters.zip

@[spec]
def Impl.new
    (I1 : Type)
    (I2 : Type)
    [trait_constr_new_associated_type_i0 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I1]
    [trait_constr_new_i0 : core_models.iter.traits.iterator.Iterator I1 ]
    [trait_constr_new_associated_type_i1 :
      core_models.iter.traits.iterator.Iterator.AssociatedTypes
      I2]
    [trait_constr_new_i1 : core_models.iter.traits.iterator.Iterator I2 ]
    (it1 : I1)
    (it2 : I2) :
    RustM (Zip I1 I2) := do
  (pure (Zip.mk (it1 := it1) (it2 := it2)))

end core_models.iter.adapters.zip


namespace core_models.iter.traits.iterator

@[reducible] instance Impl.AssociatedTypes
  (I : Type)
  [trait_constr_Impl_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_i0 : Iterator I ] :
  IteratorMethods.AssociatedTypes I
  where

instance Impl
  (I : Type)
  [trait_constr_Impl_associated_type_i0 : Iterator.AssociatedTypes I]
  [trait_constr_Impl_i0 : Iterator I ] :
  IteratorMethods I
  where
  fold :=
    fun
      (B : Type)
      (F : Type)
      [trait_constr_fold_associated_type_i1 :
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (rust_primitives.hax.Tuple2 B (Iterator.Item I))]
      [trait_constr_fold_i1 : core_models.ops.function.FnOnce
        F
        (rust_primitives.hax.Tuple2 B (Iterator.Item I))
        (associatedTypes := {
          show
            core_models.ops.function.FnOnce.AssociatedTypes
            F
            (rust_primitives.hax.Tuple2 B (Iterator.Item I))
          by infer_instance
          with Output := B})] (self : I) (init : B) (f : F) => do
    (pure init)
  enumerate := fun (self : I) => do
    (core_models.iter.adapters.enumerate.Impl.new I self)
  step_by := fun (self : I) (step : usize) => do
    (core_models.iter.adapters.step_by.Impl.new I self step)
  map :=
    fun
      (O : Type)
      (F : Type)
      [trait_constr_map_associated_type_i1 :
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (Iterator.Item I)]
      [trait_constr_map_i1 : core_models.ops.function.FnOnce
        F
        (Iterator.Item I)
        (associatedTypes := {
          show
            core_models.ops.function.FnOnce.AssociatedTypes
            F
            (Iterator.Item I)
          by infer_instance
          with Output := O})] (self : I) (f : F) => do
    (core_models.iter.adapters.map.Impl.new I F self f)
  all :=
    fun
      (F : Type)
      [trait_constr_all_associated_type_i1 :
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (Iterator.Item I)]
      [trait_constr_all_i1 : core_models.ops.function.FnOnce
        F
        (Iterator.Item I)
        (associatedTypes := {
          show
            core_models.ops.function.FnOnce.AssociatedTypes
            F
            (Iterator.Item I)
          by infer_instance
          with Output := Bool})] (self : I) (f : F) => do
    (pure true)
  take := fun (self : I) (n : usize) => do
    (core_models.iter.adapters.take.Impl.new I self n)
  flat_map :=
    fun
      (U : Type)
      (F : Type)
      [trait_constr_flat_map_associated_type_i1 : Iterator.AssociatedTypes U]
      [trait_constr_flat_map_i1 : Iterator U ]
      [trait_constr_flat_map_associated_type_i2 :
        core_models.ops.function.FnOnce.AssociatedTypes
        F
        (Iterator.Item I)]
      [trait_constr_flat_map_i2 : core_models.ops.function.FnOnce
        F
        (Iterator.Item I)
        (associatedTypes := {
          show
            core_models.ops.function.FnOnce.AssociatedTypes
            F
            (Iterator.Item I)
          by infer_instance
          with Output := U})] (self : I) (f : F) => do
    (core_models.iter.adapters.flat_map.Impl.new I U F self f)
  flatten :=
    fun
      [trait_constr_flatten_associated_type_i1 : Iterator.AssociatedTypes
        (Iterator.Item I)]
      [trait_constr_flatten_i1 : Iterator (Iterator.Item I) ] (self : I) => do
    (core_models.iter.adapters.flatten.Impl.new I self)
  zip :=
    fun
      (I2 : Type)
      [trait_constr_zip_associated_type_i1 : Iterator.AssociatedTypes I2]
      [trait_constr_zip_i1 : Iterator I2 ] (self : I) (it2 : I2) => do
    (core_models.iter.adapters.zip.Impl.new I I2 self it2)

end core_models.iter.traits.iterator


namespace core_models.iter.adapters.zip

@[instance] opaque Impl_1.AssociatedTypes
  (I1 : Type)
  (I2 : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I1]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I1 ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I2]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator I2 ] :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Zip I1 I2) :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1
  (I1 : Type)
  (I2 : Type)
  [trait_constr_Impl_1_associated_type_i0 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I1]
  [trait_constr_Impl_1_i0 : core_models.iter.traits.iterator.Iterator I1 ]
  [trait_constr_Impl_1_associated_type_i1 :
    core_models.iter.traits.iterator.Iterator.AssociatedTypes
    I2]
  [trait_constr_Impl_1_i1 : core_models.iter.traits.iterator.Iterator I2 ] :
  core_models.iter.traits.iterator.Iterator (Zip I1 I2) :=
  by constructor <;> exact Inhabited.default

end core_models.iter.adapters.zip


namespace core_models.ops.function

class Fn.AssociatedTypes (Self : Type) (Args : Type) where
  [trait_constr_Fn_i0 : FnOnce.AssociatedTypes Self Args]

attribute [instance] Fn.AssociatedTypes.trait_constr_Fn_i0

class Fn (Self : Type) (Args : Type)
  [associatedTypes : outParam (Fn.AssociatedTypes (Self : Type) (Args : Type))]
  where
  [trait_constr_Fn_i0 : FnOnce Self Args]
  call (Self) (Args) : (Self -> Args -> RustM (FnOnce.Output Self Args))

attribute [instance] Fn.trait_constr_Fn_i0

@[reducible] instance Impl_2.AssociatedTypes (Arg : Type) (Out : Type) :
  FnOnce.AssociatedTypes (Arg -> RustM Out) Arg
  where
  Output := Out

instance Impl_2 (Arg : Type) (Out : Type) : FnOnce (Arg -> RustM Out) Arg where
  call_once := fun (self : (Arg -> RustM Out)) (arg : Arg) => do (self arg)

@[reducible] instance Impl.AssociatedTypes
  (Arg1 : Type)
  (Arg2 : Type)
  (Out : Type) :
  FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> RustM Out)
  (rust_primitives.hax.Tuple2 Arg1 Arg2)
  where
  Output := Out

instance Impl (Arg1 : Type) (Arg2 : Type) (Out : Type) :
  FnOnce (Arg1 -> Arg2 -> RustM Out) (rust_primitives.hax.Tuple2 Arg1 Arg2)
  where
  call_once :=
    fun
      (self : (Arg1 -> Arg2 -> RustM Out))
      (arg : (rust_primitives.hax.Tuple2 Arg1 Arg2)) => do
    (self
      (rust_primitives.hax.Tuple2._0 arg)
      (rust_primitives.hax.Tuple2._1 arg))

@[reducible] instance Impl_1.AssociatedTypes
  (Arg1 : Type)
  (Arg2 : Type)
  (Arg3 : Type)
  (Out : Type) :
  FnOnce.AssociatedTypes
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (rust_primitives.hax.Tuple3 Arg1 Arg2 Arg3)
  where
  Output := Out

instance Impl_1 (Arg1 : Type) (Arg2 : Type) (Arg3 : Type) (Out : Type) :
  FnOnce
  (Arg1 -> Arg2 -> Arg3 -> RustM Out)
  (rust_primitives.hax.Tuple3 Arg1 Arg2 Arg3)
  where
  call_once :=
    fun
      (self : (Arg1 -> Arg2 -> Arg3 -> RustM Out))
      (arg : (rust_primitives.hax.Tuple3 Arg1 Arg2 Arg3)) => do
    (self
      (rust_primitives.hax.Tuple3._0 arg)
      (rust_primitives.hax.Tuple3._1 arg)
      (rust_primitives.hax.Tuple3._2 arg))

end core_models.ops.function


namespace core_models.ops.deref

@[reducible] instance Impl.AssociatedTypes (T : Type) :
  Deref.AssociatedTypes T
  where
  Target := T

instance Impl (T : Type) : Deref T where
  deref := fun (self : T) => do (pure self)

end core_models.ops.deref


namespace core_models.option

@[spec]
def Impl.is_some_and
    (T : Type)
    (F : Type)
    [trait_constr_is_some_and_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_some_and_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => do (pure false)
    | (Option.Some  x) => do (core_models.ops.function.FnOnce.call_once F T f x)

@[spec]
def Impl.is_none_or
    (T : Type)
    (F : Type)
    [trait_constr_is_none_or_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_is_none_or_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := Bool})]
    (self : (Option T))
    (f : F) :
    RustM Bool := do
  match self with
    | (Option.None ) => do (pure true)
    | (Option.Some  x) => do (core_models.ops.function.FnOnce.call_once F T f x)

@[spec]
def Impl.unwrap_or_else
    (T : Type)
    (F : Type)
    [trait_constr_unwrap_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_unwrap_or_else_i0 : core_models.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := T})]
    (self : (Option T))
    (f : F) :
    RustM T := do
  match self with
    | (Option.Some  x) => do (pure x)
    | (Option.None ) => do
      (core_models.ops.function.FnOnce.call_once
        F
        rust_primitives.hax.Tuple0 f rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl.map
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => do
      (pure (Option.Some
        (← (core_models.ops.function.FnOnce.call_once F T f x))))
    | (Option.None ) => do (pure Option.None)

@[spec]
def Impl.map_or
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Option.None ) => do (pure default)

@[spec]
def Impl.map_or_else
    (T : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_else_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      D
      rust_primitives.hax.Tuple0]
    [trait_constr_map_or_else_i1 : core_models.ops.function.FnOnce
      D
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          D
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := U})]
    (self : (Option T))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Option.None ) => do
      (core_models.ops.function.FnOnce.call_once
        D
        rust_primitives.hax.Tuple0 default rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl.map_or_default
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_default_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_default_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_default_associated_type_i1 :
      core_models.default.Default.AssociatedTypes
      U]
    [trait_constr_map_or_default_i1 : core_models.default.Default U ]
    (self : (Option T))
    (f : F) :
    RustM U := do
  match self with
    | (Option.Some  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Option.None ) => do
      (core_models.default.Default.default U rust_primitives.hax.Tuple0.mk)

@[spec]
def Impl.ok_or_else
    (T : Type)
    (E : Type)
    (F : Type)
    [trait_constr_ok_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      rust_primitives.hax.Tuple0]
    [trait_constr_ok_or_else_i0 : core_models.ops.function.FnOnce
      F
      rust_primitives.hax.Tuple0
      (associatedTypes := {
        show
          core_models.ops.function.FnOnce.AssociatedTypes
          F
          rust_primitives.hax.Tuple0
        by infer_instance
        with Output := E})]
    (self : (Option T))
    (err : F) :
    RustM (core_models.result.Result T E) := do
  match self with
    | (Option.Some  v) => do (pure (core_models.result.Result.Ok v))
    | (Option.None ) => do
      (pure (core_models.result.Result.Err
        (← (core_models.ops.function.FnOnce.call_once
          F
          rust_primitives.hax.Tuple0 err rust_primitives.hax.Tuple0.mk))))

@[spec]
def Impl.and_then
    (T : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_and_then_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := (Option U)})]
    (self : (Option T))
    (f : F) :
    RustM (Option U) := do
  match self with
    | (Option.Some  x) => do (core_models.ops.function.FnOnce.call_once F T f x)
    | (Option.None ) => do (pure Option.None)

end core_models.option


namespace core_models.result

@[spec]
def Impl.map
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => do
      (pure (Result.Ok
        (← (core_models.ops.function.FnOnce.call_once F T op t))))
    | (Result.Err  e) => do (pure (Result.Err e))

@[spec]
def Impl.map_or
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_map_or_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : U)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Result.Err  _e) => do (pure default)

@[spec]
def Impl.map_or_else
    (T : Type)
    (E : Type)
    (U : Type)
    (D : Type)
    (F : Type)
    [trait_constr_map_or_else_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_map_or_else_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := U})]
    [trait_constr_map_or_else_associated_type_i1 :
      core_models.ops.function.FnOnce.AssociatedTypes
      D
      E]
    [trait_constr_map_or_else_i1 : core_models.ops.function.FnOnce
      D
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes D E
        by infer_instance
        with Output := U})]
    (self : (Result T E))
    (default : D)
    (f : F) :
    RustM U := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T f t)
    | (Result.Err  e) => do
      (core_models.ops.function.FnOnce.call_once D E default e)

@[spec]
def Impl.map_err
    (T : Type)
    (E : Type)
    (F : Type)
    (O : Type)
    [trait_constr_map_err_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      O
      E]
    [trait_constr_map_err_i0 : core_models.ops.function.FnOnce
      O
      E
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes O E
        by infer_instance
        with Output := F})]
    (self : (Result T E))
    (op : O) :
    RustM (Result T F) := do
  match self with
    | (Result.Ok  t) => do (pure (Result.Ok t))
    | (Result.Err  e) => do
      (pure (Result.Err
        (← (core_models.ops.function.FnOnce.call_once O E op e))))

@[spec]
def Impl.and_then
    (T : Type)
    (E : Type)
    (U : Type)
    (F : Type)
    [trait_constr_and_then_associated_type_i0 :
      core_models.ops.function.FnOnce.AssociatedTypes
      F
      T]
    [trait_constr_and_then_i0 : core_models.ops.function.FnOnce
      F
      T
      (associatedTypes := {
        show core_models.ops.function.FnOnce.AssociatedTypes F T
        by infer_instance
        with Output := (Result U E)})]
    (self : (Result T E))
    (op : F) :
    RustM (Result U E) := do
  match self with
    | (Result.Ok  t) => do (core_models.ops.function.FnOnce.call_once F T op t)
    | (Result.Err  e) => do (pure (Result.Err e))

end core_models.result


namespace core_models.slice.iter

@[reducible] instance Impl_2.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Iter T)
  where
  Item := T

instance Impl_2 (T : Type) :
  core_models.iter.traits.iterator.Iterator (Iter T)
  where
  next := fun (self : (Iter T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.sequence.seq_len T (Iter._0 self)))
        ==? (0 : usize))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None))
      else do
        let res : T ← (rust_primitives.sequence.seq_first T (Iter._0 self));
        let self : (Iter T) :=
          {self
          with _0 := (← (rust_primitives.sequence.seq_slice T
            (Iter._0 self)
            (1 : usize)
            (← (rust_primitives.sequence.seq_len T (Iter._0 self)))))};
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_3.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (Chunks T)
  where
  Item := (RustSlice T)

instance Impl_3 (T : Type) :
  core_models.iter.traits.iterator.Iterator (Chunks T)
  where
  next := fun (self : (Chunks T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.slice.slice_length T (Chunks.elements self)))
        ==? (0 : usize))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None))
      else do
        if
        (← ((← (rust_primitives.slice.slice_length T (Chunks.elements self)))
          <? (Chunks.cs self))) then do
          let res : (RustSlice T) := (Chunks.elements self);
          let self : (Chunks T) :=
            {self
            with elements := (← (rust_primitives.slice.slice_slice T
              (Chunks.elements self)
              (0 : usize)
              (0 : usize)))};
          (pure (rust_primitives.hax.Tuple2.mk
            self
            (core_models.option.Option.Some res)))
        else do
          let ⟨res, new_elements⟩ ←
            (rust_primitives.slice.slice_split_at T
              (Chunks.elements self)
              (Chunks.cs self));
          let self : (Chunks T) := {self with elements := new_elements};
          (pure (rust_primitives.hax.Tuple2.mk
            self
            (core_models.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

@[reducible] instance Impl_4.AssociatedTypes (T : Type) :
  core_models.iter.traits.iterator.Iterator.AssociatedTypes (ChunksExact T)
  where
  Item := (RustSlice T)

instance Impl_4 (T : Type) :
  core_models.iter.traits.iterator.Iterator (ChunksExact T)
  where
  next := fun (self : (ChunksExact T)) => do
    let ⟨self, hax_temp_output⟩ ←
      if
      (← ((← (rust_primitives.slice.slice_length T (ChunksExact.elements self)))
        <? (ChunksExact.cs self))) then do
        (pure (rust_primitives.hax.Tuple2.mk
          self
          core_models.option.Option.None))
      else do
        let ⟨res, new_elements⟩ ←
          (rust_primitives.slice.slice_split_at T
            (ChunksExact.elements self)
            (ChunksExact.cs self));
        let self : (ChunksExact T) := {self with elements := new_elements};
        (pure (rust_primitives.hax.Tuple2.mk
          self
          (core_models.option.Option.Some res)));
    (pure (rust_primitives.hax.Tuple2.mk self hax_temp_output))

end core_models.slice.iter


namespace core_models.slice

@[spec]
def Impl.get
    (T : Type)
    (I : Type)
    [trait_constr_get_associated_type_i0 : SliceIndex.AssociatedTypes
      I
      (RustSlice T)]
    [trait_constr_get_i0 : SliceIndex I (RustSlice T) ]
    (s : (RustSlice T))
    (index : I) :
    RustM (core_models.option.Option (SliceIndex.Output I (RustSlice T))) := do
  (SliceIndex.get I (RustSlice T) index s)

end core_models.slice

